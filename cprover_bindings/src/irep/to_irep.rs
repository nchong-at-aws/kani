// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Converts a typed goto-program into the `Irep` serilization format of CBMC
// TODO: consider making a macro to replace `vector_map![])` for initilizing btrees.
use super::super::goto_program;
use super::super::MachineModel;
use super::{Irep, IrepId};
use crate::vector_map;
use goto_program::{
    BinaryOperand, CIntType, DatatypeComponent, Expr, ExprValue, Location, Parameter, SelfOperand,
    Stmt, StmtBody, SwitchCase, SymbolValues, Type, UnaryOperand,
};

pub trait ToIrep {
    fn to_irep(&self, mm: &MachineModel) -> Irep;
}

/// Utility functions
fn arguments_irep(arguments: &[Expr], mm: &MachineModel) -> Irep {
    Irep {
        id: IrepId::Arguments,
        sub: arguments.iter().map(|x| x.to_irep(mm)).collect(),
        named_sub: vector_map![],
    }
}
fn code_irep(kind: IrepId, ops: Vec<Irep>) -> Irep {
    Irep {
        id: IrepId::Code,
        sub: ops,
        named_sub: vector_map![(IrepId::Statement, Irep::just_id(kind))],
    }
}
fn side_effect_irep(kind: IrepId, ops: Vec<Irep>) -> Irep {
    Irep {
        id: IrepId::SideEffect,
        sub: ops,
        named_sub: vector_map![(IrepId::Statement, Irep::just_id(kind))],
    }
}
fn switch_default_irep(body: &Stmt, mm: &MachineModel) -> Irep {
    code_irep(IrepId::SwitchCase, vec![Irep::nil(), body.to_irep(mm)])
        .with_named_sub(IrepId::Default, Irep::one())
        .with_location(body.location(), mm)
}

/// ID Converters
pub trait ToIrepId {
    fn to_irep_id(&self) -> IrepId;
}

impl ToIrepId for BinaryOperand {
    fn to_irep_id(&self) -> IrepId {
        match self {
            BinaryOperand::And => IrepId::And,
            BinaryOperand::Ashr => IrepId::Ashr,
            BinaryOperand::Bitand => IrepId::Bitand,
            BinaryOperand::Bitnand => IrepId::Bitnand,
            BinaryOperand::Bitor => IrepId::Bitor,
            BinaryOperand::Bitxor => IrepId::Bitxor,
            BinaryOperand::Div => IrepId::Div,
            BinaryOperand::Equal => IrepId::Equal,
            BinaryOperand::Ge => IrepId::Ge,
            BinaryOperand::Gt => IrepId::Gt,
            BinaryOperand::IeeeFloatEqual => IrepId::IeeeFloatEqual,
            BinaryOperand::IeeeFloatNotequal => IrepId::IeeeFloatNotequal,
            BinaryOperand::Implies => IrepId::Implies,
            BinaryOperand::Le => IrepId::Le,
            BinaryOperand::Lshr => IrepId::Lshr,
            BinaryOperand::Lt => IrepId::Lt,
            BinaryOperand::Minus => IrepId::Minus,
            BinaryOperand::Mod => IrepId::Mod,
            BinaryOperand::Mult => IrepId::Mult,
            BinaryOperand::Notequal => IrepId::Notequal,
            BinaryOperand::Or => IrepId::Or,
            BinaryOperand::OverflowMinus => IrepId::OverflowMinus,
            BinaryOperand::OverflowMult => IrepId::OverflowMult,
            BinaryOperand::OverflowPlus => IrepId::OverflowPlus,
            BinaryOperand::Plus => IrepId::Plus,
            BinaryOperand::Rol => IrepId::Rol,
            BinaryOperand::Ror => IrepId::Ror,
            BinaryOperand::Shl => IrepId::Shl,
            BinaryOperand::Xor => IrepId::Xor,
        }
    }
}

impl ToIrepId for SelfOperand {
    fn to_irep_id(&self) -> IrepId {
        match self {
            SelfOperand::Postdecrement => IrepId::Postdecrement,
            SelfOperand::Postincrement => IrepId::Postincrement,
            SelfOperand::Predecrement => IrepId::Predecrement,
            SelfOperand::Preincrement => IrepId::Preincrement,
        }
    }
}

impl ToIrepId for UnaryOperand {
    fn to_irep_id(&self) -> IrepId {
        match self {
            UnaryOperand::Bitnot => IrepId::Bitnot,
            UnaryOperand::BitReverse => IrepId::BitReverse,
            UnaryOperand::Bswap => IrepId::Bswap,
            UnaryOperand::CountLeadingZeros { .. } => IrepId::CountLeadingZeros,
            UnaryOperand::CountTrailingZeros { .. } => IrepId::CountTrailingZeros,
            UnaryOperand::IsDynamicObject => IrepId::IsDynamicObject,
            UnaryOperand::IsFinite => IrepId::IsFinite,
            UnaryOperand::Not => IrepId::Not,
            UnaryOperand::ObjectSize => IrepId::ObjectSize,
            UnaryOperand::PointerObject => IrepId::PointerObject,
            UnaryOperand::PointerOffset => IrepId::PointerOffset,
            UnaryOperand::Popcount => IrepId::Popcount,
            UnaryOperand::UnaryMinus => IrepId::UnaryMinus,
        }
    }
}

/// The main converters
impl ToIrep for DatatypeComponent {
    fn to_irep(&self, mm: &MachineModel) -> Irep {
        match self {
            DatatypeComponent::Field { name, typ } => Irep::just_named_sub(vector_map![
                (IrepId::Name, Irep::just_string_id(name.to_string())),
                (IrepId::PrettyName, Irep::just_string_id(name.to_string())),
                (IrepId::Type, typ.to_irep(mm)),
            ]),
            DatatypeComponent::Padding { name, bits } => Irep::just_named_sub(vector_map![
                (IrepId::CIsPadding, Irep::one()),
                (IrepId::Name, Irep::just_string_id(name.to_string())),
                (IrepId::Type, Type::unsigned_int(*bits).to_irep(mm)),
            ]),
        }
    }
}

impl ToIrep for Expr {
    fn to_irep(&self, mm: &MachineModel) -> Irep {
        if let ExprValue::IntConstant(i) = self.value() {
            let width = self.typ().native_width(mm).unwrap();
            Irep {
                id: IrepId::Constant,
                sub: vec![],
                named_sub: vector_map![(
                    IrepId::Value,
                    Irep::just_bitpattern_id(i.clone(), width, self.typ().is_signed(mm))
                )],
            }
            .with_location(self.location(), mm)
            .with_type(self.typ(), mm)
        } else {
            self.value().to_irep(mm).with_location(self.location(), mm).with_type(self.typ(), mm)
        }
    }
}

impl ToIrep for ExprValue {
    fn to_irep(&self, mm: &MachineModel) -> Irep {
        match self {
            ExprValue::AddressOf(e) => {
                Irep { id: IrepId::AddressOf, sub: vec![e.to_irep(mm)], named_sub: vector_map![] }
            }
            ExprValue::Array { elems } => Irep {
                id: IrepId::Array,
                sub: elems.iter().map(|x| x.to_irep(mm)).collect(),
                named_sub: vector_map![],
            },
            ExprValue::ArrayOf { elem } => {
                Irep { id: IrepId::ArrayOf, sub: vec![elem.to_irep(mm)], named_sub: vector_map![] }
            }
            ExprValue::Assign { left, right } => {
                side_effect_irep(IrepId::Assign, vec![left.to_irep(mm), right.to_irep(mm)])
            }
            ExprValue::BinOp { op, lhs, rhs } => Irep {
                id: op.to_irep_id(),
                sub: vec![lhs.to_irep(mm), rhs.to_irep(mm)],
                named_sub: vector_map![],
            },
            ExprValue::BoolConstant(c) => Irep {
                id: IrepId::Constant,
                sub: vec![],
                named_sub: vector_map![(
                    IrepId::Value,
                    if *c { Irep::just_id(IrepId::True) } else { Irep::just_id(IrepId::False) },
                )],
            },
            ExprValue::ByteExtract { e, offset } => Irep {
                id: if mm.is_big_endian() {
                    IrepId::ByteExtractBigEndian
                } else {
                    IrepId::ByteExtractLittleEndian
                },
                sub: vec![e.to_irep(mm), Expr::int_constant(*offset, Type::ssize_t()).to_irep(mm)],
                named_sub: vector_map![],
            },
            ExprValue::CBoolConstant(i) => Irep {
                id: IrepId::Constant,
                sub: vec![],
                named_sub: vector_map![(
                    IrepId::Value,
                    Irep::just_bitpattern_id(if *i { 1u8 } else { 0 }, mm.bool_width(), false)
                )],
            },
            ExprValue::Dereference(e) => {
                Irep { id: IrepId::Dereference, sub: vec![e.to_irep(mm)], named_sub: vector_map![] }
            }
            //TODO, determine if there is an endineness problem here
            ExprValue::DoubleConstant(i) => {
                let c: u64 = unsafe { std::mem::transmute(*i) };
                Irep {
                    id: IrepId::Constant,
                    sub: vec![],
                    named_sub: vector_map![(
                        IrepId::Value,
                        Irep::just_bitpattern_id(c, mm.double_width(), false)
                    )],
                }
            }
            ExprValue::FloatConstant(i) => {
                let c: u32 = unsafe { std::mem::transmute(*i) };
                Irep {
                    id: IrepId::Constant,
                    sub: vec![],
                    named_sub: vector_map![(
                        IrepId::Value,
                        Irep::just_bitpattern_id(c, mm.float_width(), false)
                    )],
                }
            }
            ExprValue::FunctionCall { function, arguments } => side_effect_irep(
                IrepId::FunctionCall,
                vec![function.to_irep(mm), arguments_irep(arguments, mm)],
            ),
            ExprValue::If { c, t, e } => Irep {
                id: IrepId::If,
                sub: vec![c.to_irep(mm), t.to_irep(mm), e.to_irep(mm)],
                named_sub: vector_map![],
            },
            ExprValue::Index { array, index } => Irep {
                id: IrepId::Index,
                sub: vec![array.to_irep(mm), index.to_irep(mm)],
                named_sub: vector_map![],
            },
            ExprValue::IntConstant(_) => {
                unreachable!("Should have been processed in previous step")
            }
            ExprValue::Member { lhs, field } => Irep {
                id: IrepId::Member,
                sub: vec![lhs.to_irep(mm)],
                named_sub: vector_map![
                    (IrepId::CLvalue, Irep::one()),
                    (IrepId::ComponentName, Irep::just_string_id(field.to_string())),
                ],
            },
            ExprValue::Nondet => side_effect_irep(IrepId::Nondet, vec![]),
            ExprValue::PointerConstant(0) => Irep {
                id: IrepId::Constant,
                sub: vec![],
                named_sub: vector_map![(IrepId::Value, Irep::just_id(IrepId::NULL))],
            },
            ExprValue::PointerConstant(i) => Irep {
                id: IrepId::Constant,
                sub: vec![],
                named_sub: vector_map![(
                    IrepId::Value,
                    Irep::just_bitpattern_id(*i, mm.pointer_width(), false)
                )],
            },
            ExprValue::SelfOp { op, e } => side_effect_irep(op.to_irep_id(), vec![e.to_irep(mm)]),
            ExprValue::StatementExpression { statements: ops } => side_effect_irep(
                IrepId::StatementExpression,
                vec![Stmt::block(ops.to_vec(), Location::none()).to_irep(mm)],
            ),
            ExprValue::StringConstant { s } => Irep {
                id: IrepId::StringConstant,
                sub: vec![],
                named_sub: vector_map![(IrepId::Value, Irep::just_string_id(s.to_string()),)],
            },
            ExprValue::Struct { values } => Irep {
                id: IrepId::Struct,
                sub: values.iter().map(|x| x.to_irep(mm)).collect(),
                named_sub: vector_map![],
            },
            ExprValue::Symbol { identifier } => Irep {
                id: IrepId::Symbol,
                sub: vec![],
                named_sub: vector_map![(
                    IrepId::Identifier,
                    Irep::just_string_id(identifier.to_string()),
                )],
            },
            ExprValue::Typecast(e) => {
                Irep { id: IrepId::Typecast, sub: vec![e.to_irep(mm)], named_sub: vector_map![] }
            }
            ExprValue::Union { value, field } => Irep {
                id: IrepId::Union,
                sub: vec![value.to_irep(mm)],
                named_sub: vector_map![(
                    IrepId::ComponentName,
                    Irep::just_string_id(field.to_string()),
                )],
            },
            ExprValue::UnOp { op: UnaryOperand::Bswap, e } => Irep {
                id: IrepId::Bswap,
                sub: vec![e.to_irep(mm)],
                named_sub: vector_map![(IrepId::BitsPerByte, Irep::just_int_id(8u8))],
            },
            ExprValue::UnOp { op: UnaryOperand::BitReverse, e } => {
                Irep { id: IrepId::BitReverse, sub: vec![e.to_irep(mm)], named_sub: vector_map![] }
            }
            ExprValue::UnOp { op: UnaryOperand::CountLeadingZeros { allow_zero }, e } => Irep {
                id: IrepId::CountLeadingZeros,
                sub: vec![e.to_irep(mm)],
                named_sub: vector_map![(
                    IrepId::CBoundsCheck,
                    if *allow_zero { Irep::zero() } else { Irep::one() }
                )],
            },
            ExprValue::UnOp { op: UnaryOperand::CountTrailingZeros { allow_zero }, e } => Irep {
                id: IrepId::CountTrailingZeros,
                sub: vec![e.to_irep(mm)],
                named_sub: vector_map![(
                    IrepId::CBoundsCheck,
                    if *allow_zero { Irep::zero() } else { Irep::one() }
                )],
            },
            ExprValue::UnOp { op, e } => {
                Irep { id: op.to_irep_id(), sub: vec![e.to_irep(mm)], named_sub: vector_map![] }
            }
            ExprValue::Vector { elems } => Irep {
                id: IrepId::Vector,
                sub: elems.iter().map(|x| x.to_irep(mm)).collect(),
                named_sub: vector_map![],
            },
        }
    }
}

impl ToIrep for Location {
    fn to_irep(&self, _mm: &MachineModel) -> Irep {
        match self {
            Location::None => Irep::nil(),
            Location::BuiltinFunction { line, function_name } => Irep::just_named_sub(vector_map![
                (
                    IrepId::File,
                    Irep::just_string_id(format!("<builtin-library-{}>", function_name)),
                ),
                (IrepId::Function, Irep::just_string_id(function_name.to_string())),
            ])
            .with_named_sub_option(IrepId::Line, line.map(Irep::just_int_id)),
            Location::Loc { file, function, line, col } => Irep::just_named_sub(vector_map![
                (IrepId::File, Irep::just_string_id(file.to_string())),
                (IrepId::Line, Irep::just_int_id(*line)),
            ])
            .with_named_sub_option(IrepId::Column, col.map(Irep::just_int_id))
            .with_named_sub_option(IrepId::Function, function.map(Irep::just_string_id)),
            Location::Property { file, function, line, col, property_class, comment } => {
                Irep::just_named_sub(vector_map![
                    (IrepId::File, Irep::just_string_id(file.to_string())),
                    (IrepId::Line, Irep::just_int_id(*line)),
                ])
                .with_named_sub_option(IrepId::Column, col.map(Irep::just_int_id))
                .with_named_sub_option(IrepId::Function, function.map(Irep::just_string_id))
                .with_named_sub(IrepId::Comment, Irep::just_string_id(comment.to_string()))
                .with_named_sub(
                    IrepId::PropertyClass,
                    Irep::just_string_id(property_class.to_string()),
                )
            }
            Location::PropertyUnknownLocation { property_class, comment } => {
                Irep::just_named_sub(vector_map![
                    (IrepId::Comment, Irep::just_string_id(comment.to_string())),
                    (IrepId::PropertyClass, Irep::just_string_id(property_class.to_string()))
                ])
            }
        }
    }
}

impl ToIrep for Parameter {
    fn to_irep(&self, mm: &MachineModel) -> Irep {
        Irep {
            id: IrepId::Parameter,
            sub: vec![],
            named_sub: vector_map![(IrepId::Type, self.typ().to_irep(mm))],
        }
        .with_named_sub_option(IrepId::CIdentifier, self.identifier().map(Irep::just_string_id))
        .with_named_sub_option(IrepId::CBaseName, self.base_name().map(Irep::just_string_id))
    }
}

impl ToIrep for Stmt {
    fn to_irep(&self, mm: &MachineModel) -> Irep {
        self.body().to_irep(mm).with_location(self.location(), mm)
    }
}

impl ToIrep for StmtBody {
    fn to_irep(&self, mm: &MachineModel) -> Irep {
        match self {
            StmtBody::Assign { lhs, rhs } => {
                code_irep(IrepId::Assign, vec![lhs.to_irep(mm), rhs.to_irep(mm)])
            }
            StmtBody::Assert { cond, .. } => code_irep(IrepId::Assert, vec![cond.to_irep(mm)]),
            StmtBody::Assume { cond } => code_irep(IrepId::Assume, vec![cond.to_irep(mm)]),
            StmtBody::AtomicBlock(stmts) => {
                let mut irep_stmts = vec![code_irep(IrepId::AtomicBegin, vec![])];
                irep_stmts
                    .append(&mut stmts.into_iter().map(|x| x.to_irep(mm)).collect::<Vec<Irep>>());
                irep_stmts.push(code_irep(IrepId::AtomicEnd, vec![]));
                code_irep(IrepId::Block, irep_stmts)
            }
            StmtBody::Block(stmts) => {
                code_irep(IrepId::Block, stmts.iter().map(|x| x.to_irep(mm)).collect())
            }
            StmtBody::Break => code_irep(IrepId::Break, vec![]),
            StmtBody::Continue => code_irep(IrepId::Continue, vec![]),
            StmtBody::Decl { lhs, value } => {
                if value.is_some() {
                    code_irep(
                        IrepId::Decl,
                        vec![lhs.to_irep(mm), value.as_ref().unwrap().to_irep(mm)],
                    )
                } else {
                    code_irep(IrepId::Decl, vec![lhs.to_irep(mm)])
                }
            }
            StmtBody::Expression(e) => code_irep(IrepId::Expression, vec![e.to_irep(mm)]),
            StmtBody::For { init, cond, update, body } => code_irep(
                IrepId::For,
                vec![init.to_irep(mm), cond.to_irep(mm), update.to_irep(mm), body.to_irep(mm)],
            ),
            StmtBody::FunctionCall { lhs, function, arguments } => code_irep(
                IrepId::FunctionCall,
                vec![
                    lhs.as_ref().map_or(Irep::nil(), |x| x.to_irep(mm)),
                    function.to_irep(mm),
                    arguments_irep(arguments, mm),
                ],
            ),
            StmtBody::Goto(dest) => code_irep(IrepId::Goto, vec![])
                .with_named_sub(IrepId::Destination, Irep::just_string_id(dest.to_string())),
            StmtBody::Ifthenelse { i, t, e } => code_irep(
                IrepId::Ifthenelse,
                vec![
                    i.to_irep(mm),
                    t.to_irep(mm),
                    e.as_ref().map_or(Irep::nil(), |x| x.to_irep(mm)),
                ],
            ),
            StmtBody::Label { label, body } => code_irep(IrepId::Label, vec![body.to_irep(mm)])
                .with_named_sub(IrepId::Label, Irep::just_string_id(label.to_string())),
            StmtBody::Return(e) => {
                code_irep(IrepId::Return, vec![e.as_ref().map_or(Irep::nil(), |x| x.to_irep(mm))])
            }
            StmtBody::Skip => code_irep(IrepId::Skip, vec![]),
            StmtBody::Switch { control, cases, default } => {
                let mut switch_arms: Vec<Irep> = cases.iter().map(|x| x.to_irep(mm)).collect();
                if default.is_some() {
                    switch_arms.push(switch_default_irep(default.as_ref().unwrap(), mm));
                }
                code_irep(
                    IrepId::Switch,
                    vec![control.to_irep(mm), code_irep(IrepId::Block, switch_arms)],
                )
            }
            StmtBody::While { cond, body } => {
                code_irep(IrepId::While, vec![cond.to_irep(mm), body.to_irep(mm)])
            }
        }
    }
}

impl ToIrep for SwitchCase {
    fn to_irep(&self, mm: &MachineModel) -> Irep {
        code_irep(IrepId::SwitchCase, vec![self.case().to_irep(mm), self.body().to_irep(mm)])
            .with_location(self.body().location(), mm)
    }
}

impl goto_program::Symbol {
    pub fn to_irep(&self, mm: &MachineModel) -> super::Symbol {
        super::Symbol {
            typ: self.typ.to_irep(mm),
            value: match &self.value {
                SymbolValues::Expr(e) => e.to_irep(mm),
                SymbolValues::Stmt(s) => s.to_irep(mm),
                SymbolValues::None => Irep::nil(),
            },
            location: self.location.to_irep(mm),
            /// Unique identifier, same as key in symbol table `foo::x`
            name: self.name,
            /// Only used by verilog
            module: self.module.unwrap_or("".into()),
            /// Local identifier `x`
            base_name: self.base_name.unwrap_or("".into()),
            /// Almost always the same as base_name, but with name mangling can be relevant
            pretty_name: self.pretty_name.unwrap_or("".into()),
            /// Currently set to C. Consider creating a "rust" mode and using it in cbmc
            /// https://github.com/model-checking/kani/issues/1
            mode: self.mode.to_string().into(),

            // global properties
            is_type: self.is_type,
            is_macro: self.is_macro,
            is_exported: self.is_exported,
            is_input: self.is_input,
            is_output: self.is_output,
            is_state_var: self.is_state_var,
            is_property: self.is_property,

            // ansi-C properties
            is_static_lifetime: self.is_static_lifetime,
            is_thread_local: self.is_thread_local,
            is_lvalue: self.is_lvalue,
            is_file_local: self.is_file_local,
            is_extern: self.is_extern,
            is_volatile: self.is_volatile,
            is_parameter: self.is_parameter,
            is_auxiliary: self.is_auxiliary,
            is_weak: self.is_weak,
        }
    }
}

impl goto_program::SymbolTable {
    pub fn to_irep(&self) -> super::SymbolTable {
        let mm = self.machine_model();
        let mut st = super::SymbolTable::new();
        for (_key, value) in self.iter() {
            st.insert(value.to_irep(mm))
        }
        st
    }
}

impl ToIrep for Type {
    fn to_irep(&self, mm: &MachineModel) -> Irep {
        match self {
            Type::Array { typ, size } => {
                //CBMC expects the size to be a signed int constant.
                let size = Expr::int_constant(*size, Type::ssize_t());
                Irep {
                    id: IrepId::Array,
                    sub: vec![typ.to_irep(mm)],
                    named_sub: vector_map![(IrepId::Size, size.to_irep(mm))],
                }
            }
            //TODO make from_irep that matches this.
            Type::CBitField { typ, width } => Irep {
                id: IrepId::CBitField,
                sub: vec![typ.to_irep(mm)],
                named_sub: vector_map![(IrepId::Width, Irep::just_int_id(*width))],
            },
            Type::Bool => Irep::just_id(IrepId::Bool),
            Type::CInteger(CIntType::Bool) => Irep {
                id: IrepId::CBool,
                sub: vec![],
                named_sub: vector_map![(IrepId::Width, Irep::just_int_id(mm.bool_width()))],
            },
            Type::CInteger(CIntType::Char) => Irep {
                id: if mm.char_is_unsigned() { IrepId::Unsignedbv } else { IrepId::Signedbv },
                sub: vec![],
                named_sub: vector_map![(IrepId::Width, Irep::just_int_id(mm.char_width()),)],
            },
            Type::CInteger(CIntType::Int) => Irep {
                id: IrepId::Signedbv,
                sub: vec![],
                named_sub: vector_map![(IrepId::Width, Irep::just_int_id(mm.int_width()),)],
            },
            Type::CInteger(CIntType::SizeT) => Irep {
                id: IrepId::Unsignedbv,
                sub: vec![],
                named_sub: vector_map![(IrepId::Width, Irep::just_int_id(mm.pointer_width()),)],
            },
            Type::CInteger(CIntType::SSizeT) => Irep {
                id: IrepId::Signedbv,
                sub: vec![],
                named_sub: vector_map![(IrepId::Width, Irep::just_int_id(mm.pointer_width()),)],
            },
            Type::Code { parameters, return_type } => Irep {
                id: IrepId::Code,
                sub: vec![],
                named_sub: vector_map![
                    (
                        IrepId::Parameters,
                        Irep::just_sub(parameters.iter().map(|x| x.to_irep(mm)).collect()),
                    ),
                    (IrepId::ReturnType, return_type.to_irep(mm)),
                ],
            },
            Type::Constructor => Irep::just_id(IrepId::Constructor),
            Type::Double => Irep {
                id: IrepId::Floatbv,
                sub: vec![],
                named_sub: vector_map![
                    (IrepId::F, Irep::just_int_id(52)),
                    (IrepId::Width, Irep::just_int_id(64)),
                    (IrepId::CCType, Irep::just_id(IrepId::Double)),
                ],
            },
            Type::Empty => Irep::just_id(IrepId::Empty),
            // CMBC currently represents these as 0 length arrays.
            Type::FlexibleArray { typ } => {
                //CBMC expects the size to be a signed int constant.
                let size = Type::ssize_t().zero();
                Irep {
                    id: IrepId::Array,
                    sub: vec![typ.to_irep(mm)],
                    named_sub: vector_map![(IrepId::Size, size.to_irep(mm))],
                }
            }
            Type::Float => Irep {
                id: IrepId::Floatbv,
                sub: vec![],
                named_sub: vector_map![
                    (IrepId::F, Irep::just_int_id(23)),
                    (IrepId::Width, Irep::just_int_id(32)),
                    (IrepId::CCType, Irep::just_id(IrepId::Float)),
                ],
            },
            Type::IncompleteStruct { tag } => Irep {
                id: IrepId::Struct,
                sub: vec![],
                named_sub: vector_map![
                    (IrepId::Tag, Irep::just_string_id(tag.to_string())),
                    (IrepId::Incomplete, Irep::one()),
                ],
            },
            Type::IncompleteUnion { tag } => Irep {
                id: IrepId::Union,
                sub: vec![],
                named_sub: vector_map![
                    (IrepId::Tag, Irep::just_string_id(tag.to_string())),
                    (IrepId::Incomplete, Irep::one()),
                ],
            },
            Type::InfiniteArray { typ } => {
                let infinity = Irep::just_id(IrepId::Infinity).with_type(&Type::ssize_t(), mm);
                Irep {
                    id: IrepId::Array,
                    sub: vec![typ.to_irep(mm)],
                    named_sub: vector_map![(IrepId::Size, infinity)],
                }
            }
            Type::Pointer { typ } => Irep {
                id: IrepId::Pointer,
                sub: vec![typ.to_irep(mm)],
                named_sub: vector_map![(IrepId::Width, Irep::just_int_id(mm.pointer_width()),)],
            },
            Type::Signedbv { width } => Irep {
                id: IrepId::Signedbv,
                sub: vec![],
                named_sub: vector_map![(IrepId::Width, Irep::just_int_id(*width))],
            },
            Type::Struct { tag, components } => Irep {
                id: IrepId::Struct,
                sub: vec![],
                named_sub: vector_map![
                    (IrepId::Tag, Irep::just_string_id(tag.to_string())),
                    (
                        IrepId::Components,
                        Irep::just_sub(components.iter().map(|x| x.to_irep(mm)).collect()),
                    ),
                ],
            },
            Type::StructTag(name) => Irep {
                id: IrepId::StructTag,
                sub: vec![],
                named_sub: vector_map![(
                    IrepId::Identifier,
                    Irep::just_string_id(name.to_string()),
                )],
            },
            Type::Union { tag, components } => Irep {
                id: IrepId::Union,
                sub: vec![],
                named_sub: vector_map![
                    (IrepId::Tag, Irep::just_string_id(tag.to_string())),
                    (
                        IrepId::Components,
                        Irep::just_sub(components.iter().map(|x| x.to_irep(mm)).collect()),
                    ),
                ],
            },
            Type::UnionTag(name) => Irep {
                id: IrepId::UnionTag,
                sub: vec![],
                named_sub: vector_map![(
                    IrepId::Identifier,
                    Irep::just_string_id(name.to_string()),
                )],
            },
            Type::Unsignedbv { width } => Irep {
                id: IrepId::Unsignedbv,
                sub: Vec::new(),
                named_sub: vector_map![(IrepId::Width, Irep::just_int_id(*width))],
            },
            Type::VariadicCode { parameters, return_type } => Irep {
                id: IrepId::Code,
                sub: vec![],
                named_sub: vector_map![
                    (
                        IrepId::Parameters,
                        Irep::just_sub(parameters.iter().map(|x| x.to_irep(mm)).collect())
                            .with_named_sub(IrepId::Ellipsis, Irep::one()),
                    ),
                    (IrepId::ReturnType, return_type.to_irep(mm)),
                ],
            },
            Type::Vector { typ, size } => {
                let size = Expr::int_constant(*size, Type::ssize_t());
                Irep {
                    id: IrepId::Vector,
                    sub: vec![typ.to_irep(mm)],
                    named_sub: vector_map![(IrepId::Size, size.to_irep(mm))],
                }
            }
        }
    }
}
