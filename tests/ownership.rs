//! Compile-fail checks: a decode job borrows its scratch arena exclusively.
use std::{path::Path, process::Command};

#[test]
fn job_ownership() {
    let script = Path::new(env!("CARGO_MANIFEST_DIR")).join("tools/check-ownership.py");
    let result = Command::new("python3").arg(script).output().unwrap();
    assert!(
        result.status.success(),
        "check-ownership.py: {}{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
}
