// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// This test is to make sure we are correctly printing warnings from the kani-compiler.

// FIXME: This should also print a warning:
// https://github.com/model-checking/kani/issues/922
pub fn asm() {
    unsafe {
        std::arch::asm!("NOP");
    }
}

fn is_true(b: bool) {
    assert!(b);
}

// Duplicate proof harness attributes should produce a warning
#[kani::proof]
#[kani::proof]
fn harness() {
    is_true(true);
}
