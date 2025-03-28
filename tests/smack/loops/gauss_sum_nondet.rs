// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// cbmc-flags: --unwind 5

#[kani::proof]
fn main() {
    let mut sum = 0;
    let b: u64 = kani::any();
    if b < 5 && b > 1 {
        for i in 0..b {
            sum += i;
        }
        assert!(2 * sum == b * (b - 1));
    }
}
