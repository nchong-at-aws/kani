// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR MIT

// kani-flags: --function harness

// This test is to check Kani's error handling for missing functions.
// TODO: Verify that this prints a compiler warning:
//  - https://github.com/model-checking/kani/issues/576


extern "C" {
    fn missing_function() -> u32;
}

#[kani::proof]
fn harness() {
    let x = unsafe { missing_function() };
    assert!(x == 5);
}
