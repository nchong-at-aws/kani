// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR MIT

// cbmc-flags: --unwind 11

#[kani::proof]
fn main() {
    let mut a: u32 = kani::any();

    if a < 1024 {
        while a > 0 {
            a = a / 2;
        }

        assert!(a == 0);
    }
}
