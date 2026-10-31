use std::{
    env,
    fs::{self, read_dir},
    path::PathBuf,
};

fn _fail_on_empty_directory(name: &str) {
    if fs::read_dir(name).unwrap().count() == 0 {
        println!(
            "The `{}` directory is empty, did you forget to pull the submodules?",
            name
        );
        println!("Try `git submodule update --init --recursive`");
        panic!();
    }
}

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    // The vendored C++ is compiled here, so an edit to it must re-run this script.
    println!("cargo:rerun-if-changed=minisketch/src");
    println!("cargo:rerun-if-changed=minisketch/include");

    build_lib();
    generate_bindings();
}

fn build_lib() {
    let target_arch = env::var("CARGO_CFG_TARGET_ARCH").unwrap();
    let native_target = env::var("HOST").unwrap() == env::var("TARGET").unwrap();
    // Collect minisketch.cpp and .cpp files from fields/ directory
    let fields = read_dir("minisketch/src/fields").unwrap();
    let src_files = read_dir("minisketch/src")
        .unwrap()
        .chain(fields)
        .map(|f| f.unwrap())
        .filter(|f| !f.file_name().to_string_lossy().contains("test.cpp"))
        .filter(|f| !f.file_name().to_string_lossy().contains("bench.cpp"))
        .filter(|f| f.file_name().to_string_lossy().ends_with(".cpp"))
        .filter(|f| {
            let name = f.file_name().to_string_lossy().to_string();
            !(target_arch == "aarch64" && name.starts_with("clmul_"))
        })
        .map(|f| f.path())
        .collect::<Vec<_>>();

    // Build minisketch library with optimizations
    let mut build = cc::Build::new();
    build
        .files(src_files)
        .cpp(true)
        .opt_level(3)
        .debug(false)
        .warnings(false)
        .extra_warnings(false)
        .flag("-w")
        .flag("-std=c++11")
        .define("HAVE_CLZ", None);

    // Add architecture-specific optimizations
    if target_arch == "x86_64" {
        build.define("HAVE_CLMUL", None);
        if native_target {
            build.flag("-march=native");
        }
        build.flag("-mpclmul");
        build.flag("-msse4.1");
    } else if target_arch == "aarch64" && native_target {
        build.flag("-mcpu=native");
    }

    build.compile("libminisketch.a")
}

fn generate_bindings() {
    let bindings = bindgen::Builder::default()
        .generate_comments(false)
        .header("minisketch/include/minisketch.h")
        .whitelist_type("minisketch")
        .opaque_type("minisketch")
        // We'll redefine Clone, Copy and Drop by utilizing minisketch_clone() and minisketch_destroy()
        .no_copy("minisketch")
        .whitelist_function("minisketch_.+") // Bind to all minisketch_...() functions
        .generate()
        .expect("Unable to generate bindings");

    // Write the bindings to the $OUT_DIR/bindings.rs file.
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
