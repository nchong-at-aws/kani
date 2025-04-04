// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR MIT

// TODO: When unwind is hooked up, `harness.expected` should now see success
#[kani::proof]
#[kani::unwind(9)]
fn harness() {
    let mut counter = 0;
    loop {
        counter += 1;
        assert!(counter < 10);
    }
}

#[kani::proof]
fn harness_2() {
    let mut counter = 0;
    loop {
        counter += 1;
        assert!(counter < 10);
    }
}
