// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR MIT

// kani-flags: --no-unwinding-checks --verbose

// This test is to check Kani's error handling for harnesses that have multiple proof annotations
// declared.

#[kani::proof]
fn main() {
    assert!(1 == 2);
}

#[kani::proof]
#[kani::test_annotation]
fn harness() {
    let mut counter = 0;
    loop {
        counter += 1;
        assert!(counter < 10);
    }
}
