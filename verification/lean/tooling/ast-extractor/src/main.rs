//! Narrow, unverified source-AST translator. It does not certify Rust semantics.
use std::{collections::BTreeSet, env, error::Error, fs, path::Path};
use quote::ToTokens;
use syn::{BinOp, Expr, Item, Lit, Member, Pat, Stmt};

fn expression(expr: &Expr, bound: &BTreeSet<String>) -> Result<(String, String), String> {
    match expr {
        Expr::Field(field) => {
            if field.base.to_token_stream().to_string() != "product" {
                return Err("field base must be the RawProduct input".into());
            }
            match &field.member {
                Member::Named(id) if id == "lo" => Ok(("lo".into(), "(field product lo)".into())),
                Member::Named(id) if id == "hi" => Ok(("hi".into(), "(field product hi)".into())),
                _ => Err("unsupported field".into()),
            }
        }
        Expr::Path(path) if path.qself.is_none() && path.path.segments.len() == 1 => {
            let id = path.path.segments[0].ident.to_string();
            if !bound.contains(&id) {
                return Err(format!("unbound identifier: {id}"));
            }
            Ok((id.clone(), id))
        }
        Expr::Paren(paren) => expression(&paren.expr, bound),
        Expr::Group(group) => expression(&group.expr, bound),
        Expr::Binary(binary) => {
            let (left, left_ast) = expression(&binary.left, bound)?;
            match binary.op {
                BinOp::BitXor(_) => {
                    let (right, right_ast) = expression(&binary.right, bound)?;
                    Ok((format!("({left} ^^^ {right})"), format!("(xor {left_ast} {right_ast})")))
                }
                BinOp::Shl(_) | BinOp::Shr(_) => {
                    let Expr::Lit(literal) = binary.right.as_ref() else {
                        return Err("only literal shifts are supported".into());
                    };
                    let Lit::Int(integer) = &literal.lit else {
                        return Err("shift must be an integer literal".into());
                    };
                    if !integer.suffix().is_empty() {
                        return Err("suffixed shift literals are unsupported".into());
                    }
                    let shift = integer.base10_parse::<u32>().map_err(|e| e.to_string())?;
                    if shift >= 64 {
                        return Err("u64 shift is out of range".into());
                    }
                    let (lean, ast) = if matches!(binary.op, BinOp::Shl(_)) {
                        ("<<<", "shl64")
                    } else {
                        (">>>", "shr64")
                    };
                    Ok((format!("({left} {lean} {shift})"), format!("({ast} {left_ast} {shift})")))
                }
                _ => Err("only XOR and checked literal shifts are supported".into()),
            }
        }
        _ => Err(format!("unsupported expression: {}", expr.to_token_stream())),
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = env::args().collect();
    if args.len() != 3 {
        return Err("usage: bulksketch-narrow-extractor SOURCE_ROOT OUTPUT_DIRECTORY".into());
    }
    let source_root = Path::new(&args[1]);
    let output = Path::new(&args[2]);
    let field_source = fs::read_to_string(source_root.join("src/field/mod.rs"))?;
    let field = syn::parse_file(&field_source)?;
    let field_impl = field.items.iter().find_map(|item| match item {
        Item::Impl(item) if item.self_ty.to_token_stream().to_string() == "Gf64"
            && item.trait_.as_ref().is_some_and(|(_, path, _)| path.to_token_stream().to_string() == "BinaryField") => Some(item),
        _ => None,
    }).ok_or("missing Gf64 BinaryField implementation")?;
    let bits = field_impl.items.iter().find_map(|item| match item {
        syn::ImplItem::Const(item) if item.ident == "BITS" => Some(item.expr.to_token_stream().to_string()),
        _ => None,
    }).ok_or("missing Gf64::BITS")?;
    if bits != "64" {
        return Err("this extraction requires actual Gf64::BITS = 64".into());
    }
    let types = syn::parse_file(&fs::read_to_string(source_root.join("src/types.rs"))?)?;
    let raw = types.items.iter().find_map(|item| match item {
        Item::Struct(item) if item.ident == "RawProduct" => Some(item),
        _ => None,
    }).ok_or("missing RawProduct")?;
    if raw.fields.len() != 2 || raw.fields.iter().zip(["lo", "hi"]).any(|(field, id)| {
        field.ident.as_ref().map(ToString::to_string).as_deref() != Some(id)
            || field.ty.to_token_stream().to_string() != "u64"
    }) {
        return Err("RawProduct must have exactly lo:u64 and hi:u64".into());
    }
    let source = fs::read_to_string(source_root.join("src/field/gf64.rs"))?;
    let file = syn::parse_file(&source)?;
    let functions: Vec<_> = file.items.iter().filter_map(|item| match item {
        Item::Fn(item) if item.sig.ident == "reduce" => Some(item),
        _ => None,
    }).collect();
    if functions.len() != 1 {
        return Err("expected exactly one reduce function".into());
    }
    let function = functions[0];
    let signature = function.sig.to_token_stream().to_string();
    if signature != "fn reduce < F : BinaryField > (product : RawProduct) -> u64" {
        return Err(format!("unsupported signature: {signature}").into());
    }
    let [Stmt::Expr(Expr::If(branch), None)] = function.block.stmts.as_slice() else {
        return Err("reduce must consist of one tail if-expression".into());
    };
    if branch.cond.to_token_stream().to_string() != "F :: BITS == 64" || branch.else_branch.is_none() {
        return Err("expected original GF64 branch and preserved generic else".into());
    }
    if !matches!(branch.then_branch.stmts.last(), Some(Stmt::Expr(_, None))) {
        return Err("GF64 branch must end with an unsemicolonized expression".into());
    }
    let mut bound = BTreeSet::new();
    let mut lean = String::from("import Init\n\n/-! GENERATED from the pinned native Rust reduce::<Gf64> branch.\nThe AST translator and the Rust-to-BitVec semantic link are UNPROVED.\nThis definition is a model artifact, not a verified Rust implementation. -/\n\nnamespace BulksketchProofs.Generated\n\ndef reduceGf64 (lo hi : BitVec 64) : BitVec 64 :=\n");
    let mut ast = String::from("(specialize reduce Gf64 (condition (= Gf64.BITS 64))\n");
    for (index, statement) in branch.then_branch.stmts.iter().enumerate() {
        match statement {
            Stmt::Local(local) => {
                if !local.attrs.is_empty() {
                    return Err("binding attributes are unsupported".into());
                }
                let Pat::Ident(pattern) = &local.pat else { return Err("unsupported binding pattern".into()); };
                if pattern.mutability.is_some() || pattern.by_ref.is_some() || pattern.subpat.is_some() {
                    return Err("only immutable identifier bindings are supported".into());
                }
                let id = pattern.ident.to_string();
                if !matches!(id.as_str(), "high" | "overflow") || bound.contains(&id) {
                    return Err("unsupported or repeated binding identifier".into());
                }
                let init = local.init.as_ref().ok_or("binding needs initializer")?;
                if init.diverge.is_some() { return Err("let-else is unsupported".into()); }
                let (value, tree) = expression(&init.expr, &bound)?;
                lean.push_str(&format!("  let {id} := {value}\n"));
                ast.push_str(&format!("  (let {id} {tree})\n"));
                bound.insert(id);
            }
            Stmt::Expr(value, None) if index + 1 == branch.then_branch.stmts.len() => {
                let (value, tree) = expression(value, &bound)?;
                lean.push_str(&format!("  {value}\n\nend BulksketchProofs.Generated\n"));
                ast.push_str(&format!("  (return {tree}))\n"));
            }
            _ => return Err("unsupported statement or non-tail expression".into()),
        }
    }
    fs::create_dir_all(output)?;
    fs::write(output.join("Reduce.lean"), lean)?;
    fs::write(output.join("reduce-gf64.ast.sexp"), ast)?;
    fs::write(output.join("reduce-rust-body.tokens"), function.block.to_token_stream().to_string())?;
    fs::write(output.join("reduce-rust-signature.tokens"), signature)?;
    println!("extracted reduce::<Gf64> model; Rust semantic correspondence remains unproved");
    Ok(())
}
