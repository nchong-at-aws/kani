//! This module analyzes crates to find call sites that can serve as examples in the documentation.

use crate::html::render::Context;

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::{
    self as hir,
    intravisit::{self, Visitor},
};
use rustc_macros::{Decodable, Encodable};
use rustc_middle::hir::map::Map;
use rustc_middle::hir::nested_filter;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::{
    def_id::{CrateNum, DefPathHash},
    edition::Edition,
    BytePos, FileName, SourceFile,
};

use std::fs;
use std::path::PathBuf;

#[derive(Encodable, Decodable, Debug, Clone)]
crate struct SyntaxRange {
    crate byte_span: (u32, u32),
    crate line_span: (usize, usize),
}

impl SyntaxRange {
    fn new(span: rustc_span::Span, file: &SourceFile) -> Self {
        let get_pos = |bytepos: BytePos| file.original_relative_byte_pos(bytepos).0;
        let get_line = |bytepos: BytePos| file.lookup_line(bytepos).unwrap();

        SyntaxRange {
            byte_span: (get_pos(span.lo()), get_pos(span.hi())),
            line_span: (get_line(span.lo()), get_line(span.hi())),
        }
    }
}

#[derive(Encodable, Decodable, Debug, Clone)]
crate struct CallLocation {
    crate call_expr: SyntaxRange,
    crate enclosing_item: SyntaxRange,
}

impl CallLocation {
    fn new(
        expr_span: rustc_span::Span,
        enclosing_item_span: rustc_span::Span,
        source_file: &SourceFile,
    ) -> Self {
        CallLocation {
            call_expr: SyntaxRange::new(expr_span, source_file),
            enclosing_item: SyntaxRange::new(enclosing_item_span, source_file),
        }
    }
}

#[derive(Encodable, Decodable, Debug, Clone)]
crate struct CallData {
    crate locations: Vec<CallLocation>,
    crate url: String,
    crate display_name: String,
    crate edition: Edition,
}

crate type FnCallLocations = FxHashMap<PathBuf, CallData>;
crate type AllCallLocations = FxHashMap<DefPathHash, FnCallLocations>;

/// Visitor for traversing a crate and finding instances of function calls.
struct FindCalls<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    map: Map<'tcx>,
    cx: Context<'tcx>,
    target_crates: Vec<CrateNum>,
    calls: &'a mut AllCallLocations,
}

impl<'a, 'tcx> Visitor<'tcx> for FindCalls<'a, 'tcx>
where
    'tcx: 'a,
{
    type NestedFilter = nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.map
    }

    fn visit_expr(&mut self, ex: &'tcx hir::Expr<'tcx>) {
        intravisit::walk_expr(self, ex);

        let tcx = self.tcx;

        // If we visit an item that contains an expression outside a function body,
        // then we need to exit before calling typeck (which will panic). See
        // test/run-make/rustdoc-scrape-examples-invalid-expr for an example.
        let hir = tcx.hir();
        let owner = hir.local_def_id_to_hir_id(ex.hir_id.owner);
        if hir.maybe_body_owned_by(owner).is_none() {
            return;
        }

        // Get type of function if expression is a function call
        let (ty, span) = match ex.kind {
            hir::ExprKind::Call(f, _) => {
                let types = tcx.typeck(ex.hir_id.owner);

                if let Some(ty) = types.node_type_opt(f.hir_id) {
                    (ty, ex.span)
                } else {
                    trace!("node_type_opt({}) = None", f.hir_id);
                    return;
                }
            }
            hir::ExprKind::MethodCall(_, _, span) => {
                let types = tcx.typeck(ex.hir_id.owner);
                let def_id = if let Some(def_id) = types.type_dependent_def_id(ex.hir_id) {
                    def_id
                } else {
                    trace!("type_dependent_def_id({}) = None", ex.hir_id);
                    return;
                };
                (tcx.type_of(def_id), span)
            }
            _ => {
                return;
            }
        };

        // If this span comes from a macro expansion, then the source code may not actually show
        // a use of the given item, so it would be a poor example. Hence, we skip all uses in macros.
        if span.from_expansion() {
            trace!("Rejecting expr from macro: {:?}", span);
            return;
        }

        // If the enclosing item has a span coming from a proc macro, then we also don't want to include
        // the example.
        let enclosing_item_span = tcx
            .hir()
            .span_with_body(tcx.hir().local_def_id_to_hir_id(tcx.hir().get_parent_item(ex.hir_id)));
        if enclosing_item_span.from_expansion() {
            trace!("Rejecting expr ({:?}) from macro item: {:?}", span, enclosing_item_span);
            return;
        }

        assert!(
            enclosing_item_span.contains(span),
            "Attempted to scrape call at [{:?}] whose enclosing item [{:?}] doesn't contain the span of the call.",
            span,
            enclosing_item_span
        );

        // Save call site if the function resolves to a concrete definition
        if let ty::FnDef(def_id, _) = ty.kind() {
            if self.target_crates.iter().all(|krate| *krate != def_id.krate) {
                trace!("Rejecting expr from crate not being documented: {:?}", span);
                return;
            }

            let file = tcx.sess.source_map().lookup_char_pos(span.lo()).file;
            let file_path = match file.name.clone() {
                FileName::Real(real_filename) => real_filename.into_local_path(),
                _ => None,
            };

            if let Some(file_path) = file_path {
                let abs_path = fs::canonicalize(file_path.clone()).unwrap();
                let cx = &self.cx;
                let mk_call_data = || {
                    let clean_span = crate::clean::types::Span::new(span);
                    let url = cx.href_from_span(clean_span, false).unwrap();
                    let display_name = file_path.display().to_string();
                    let edition = span.edition();
                    CallData { locations: Vec::new(), url, display_name, edition }
                };

                let fn_key = tcx.def_path_hash(def_id.clone());
                let fn_entries = self.calls.entry(fn_key).or_default();

                trace!("Including expr: {:?}", span);
                let location = CallLocation::new(span, enclosing_item_span, &file);
                fn_entries.entry(abs_path).or_insert_with(mk_call_data).locations.push(location);
            }
        }
    }
}
