#!/usr/bin/env python3
"""Bind the one frozen sum_costs Iterator::try_fold call to a typed std slot.

The native caller, argument operands, closure body and unwind blocks stay
as captured. The stock translator still performs all source borrow checks.
"""

import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

RAW_SHA256 = "2be801cb47ed251d5b86d28d8c0b9a06afa6b761ae89ba4e55ee0270b6647d2b"
SPECIALIZED_SHA256 = "5c97bf7d74f619777524d05d904c12bcca819e5dc5e90f16658bce9a747e0dbf"
SELECTOR = "bulksketch::decode::work::sum_costs"
ITERATOR = "core::iter::traits::iterator::Iterator"
STD_METHOD = ITERATOR + "::try_fold"
SLOT = "bulksketch::decode::work::checked_sum_costs_slice_try_fold"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def name(text):
    return [{"Ident": [part, 0]} for part in text.split("::")]


def specialize(raw):
    require(sha256(raw).hexdigest() == RAW_SHA256, "frozen sum_costs LLBC differs")
    doc = json.loads(raw)
    crate = doc["translated"]
    options = crate["options"]
    require(doc["has_errors"] is False and options["preset"] == "Aeneas"
            and options["start_from"] == [SELECTOR] and options["opaque"] == []
            and options["no_dedup_serialized_ast"] is True,
            "sum_costs capture options differ")
    target_info, = crate["target_information"]
    require(target_info["key"] == "x86_64-apple-darwin"
            and target_info["value"]["target_pointer_size"] == 8, "capture target differs")
    source = crate["fun_decls"][11]
    method = crate["fun_decls"][21]
    require(source["item_meta"]["name"] == name(SELECTOR)
            and method["item_meta"]["name"] == name(STD_METHOD) and method["body"] == "Opaque",
            "source caller or standard method differs")

    calls = [
        node["kind"]["Call"] for node in source["body"]["Structured"]["body"]["statements"]
        if isinstance(node["kind"], dict) and "Call" in node["kind"]
    ]
    require(len(calls) == 2 and calls[0]["call"]["func"]["Regular"]["kind"] == {"Fun": 20},
            "source slice iterator construction differs")
    folded = calls[1]["call"]
    function = folded["func"]["Regular"]
    generic = function["generics"]
    require(function["kind"] == {"Fun": 21} and len(folded["args"]) == 3
            and len(generic["regions"]) == 1 and len(generic["types"]) == 5
            and len(generic["trait_refs"]) == 4, "concrete standard call differs")
    iter_type, accumulator, closure_type, output, item_type = map(deepcopy, generic["types"])
    iter_adt = iter_type["Untagged"]["Adt"]
    closure_adt = closure_type["Untagged"]["Adt"]
    slice_region, = iter_adt["generics"]["regions"]
    require(iter_adt["id"] == 8 and closure_adt["id"] == 9
            and closure_adt["generics"]["regions"] == [slice_region]
            and item_type["Untagged"]["Ref"][2] == "Shared",
            "shared iterator and closure instantiation differ")
    require(accumulator == {"Untagged": {"Scalar": {"Integer": {"Unsigned": "U64"}}}}
            and output == source["signature"]["output"]
            and folded["args"][1]["Const"]["Untagged"] == [
                {"Integer": {"Unsigned": ["U64", "0"]}}, accumulator,
            ], "checked u64/result instantiation differs")
    iterator_impl = generic["trait_refs"][0]["skip_binder"]["Untagged"]["kind"]["TraitImpl"]
    closure_impl = generic["trait_refs"][1]["skip_binder"]["Untagged"]["kind"]["TraitImpl"]
    require(iterator_impl["id"] == 6 and closure_impl["id"] == 7, "resolved iterator or callback differs")

    # Preserve the original mutable borrow and the shared slice lifetime.
    method["item_meta"]["name"] = name(SLOT)
    method["src"] = "Normal"
    regions = method["generics"]["regions"]
    require(len(regions) == 1, "generic receiver lifetime differs")
    regions.append(dict(regions[0], index=1))
    for key in ("types", "trait_clauses", "trait_type_constraints"):
        method["generics"][key] = []
    iter_adt["generics"]["regions"] = [{"Var": {"Free": 1}}]
    closure_adt["generics"]["regions"] = [{"Var": {"Free": 1}}]
    method["signature"]["inputs"] = [
        {"Untagged": {"Ref": [{"Var": {"Free": 0}}, iter_type, "Mut"]}},
        accumulator,
        closure_type,
    ]
    method["signature"]["output"] = output
    method["generics"]["outlives"][0]["skip_binder"][0]["Lub"] = iter_type
    generic["regions"].append(slice_region)
    for key in ("types", "trait_refs", "const_generics"):
        generic[key] = []
    for item in crate["item_names"]:
        if item["key"] == {"Fun": 21}:
            item["value"] = name(SLOT)

    # The generic method is unused after the concrete binding. Keep all
    # neighboring Iterator slots and concrete Result builtin call bodies.
    iterator_trait = crate["trait_decls"][4]
    require(iterator_trait["item_meta"]["name"] == name(ITERATOR)
            and iterator_trait["methods"][36]["skip_binder"]["name"] == "try_fold",
            "generic Iterator method differs")
    iterator_trait["methods"][36] = None
    for impl in crate["trait_impls"]:
        if impl and impl["impl_trait"]["id"] == 4:
            impl["methods"][36] = None
    # These dictionary groups were reachable only through the generic
    # call. Their declarations remain available for builtin resolution.
    omitted = [
        {"TraitDecl": {"NonRec": 24}},
        {"TraitDecl": {"Rec": [7, 12]}},
        {"TraitImpl": {"Rec": [8, 13]}},
    ]
    require(all(crate["ordered_decls"].count(group) == 1 for group in omitted),
            "generic Try dictionary groups differ")
    crate["ordered_decls"] = [group for group in crate["ordered_decls"] if group not in omitted]
    transformed = json.dumps(doc, separators=(",", ":")).encode()
    require(sha256(transformed).hexdigest() == SPECIALIZED_SHA256, "specialization changed")
    return transformed


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("raw", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_bytes(specialize(args.raw.read_bytes()))
