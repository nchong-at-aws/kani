// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR MIT

// This test checks that Kani reports UNDETERMINED if the specified unwinding is
// insufficient. The minimum required unwinding is 7.

// kani-flags: --unwind 6

#[kani::proof]
fn main() {
    let x: bool = kani::any();
    let v = if x { vec![1, 2, 3] } else { vec![1, 1, 1, 1, 1, 1] };

    let mut sum = 0;
    for i in v {
        sum += i;
    }
    assert!(sum == 6);
}
