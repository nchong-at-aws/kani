// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR MIT
#[derive(Debug, PartialEq)]
pub enum EnumSingle {
    MySingle(u32),
}

#[kani::proof]
fn main() {
    let e = EnumSingle::MySingle(1);
    assert!(e == EnumSingle::MySingle(1));
}
