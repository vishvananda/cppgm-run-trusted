# PA25 Audit

## Audit Plan

Contract sources to inspect:

- `TESTING_AND_REFERENCES.md`
- `pa25/README.md`
- `pa25/plan.md`
- PA25 tests under `pa25/tests/general/` and `pa25/tests/spec/`
- Through-stage evidence from `make test-report-through-pa25`
- File-audit evidence from `perl scripts/cppgm_file_audit.pl --stage pa25 --paths dev/src`

Implementation files changed by the PA25 stage commit:

- `dev/frontend_source_sets.mk`
- `dev/src/pa12_decls_declare_one.cpp`
- `dev/src/pa12_decls_initializers.cpp`
- `dev/src/pa12_expr.cpp`
- `dev/src/pa12_expr_call_helpers.cpp`
- `dev/src/pa12_expr_ids.cpp`
- `dev/src/pa12_expr_nodes.cpp`
- `dev/src/pa12_expr_primary.cpp`
- `dev/src/pa12_expr_semantics.cpp`
- `dev/src/pa12_expr_semantics_constructors.cpp`
- `dev/src/pa12_internal.h`
- `dev/src/pa12_records.cpp`
- `dev/src/pa12_statements.cpp`
- `dev/src/pa12_templates_function_deduce_call.cpp`
- `dev/src/pa14_lowir.cpp`
- `dev/src/pa14_lowir_call.cpp`
- `dev/src/pa14_lowir_function_order.cpp`
- `dev/src/pa14_lowir_init.cpp`
- `dev/src/pa14_lowir_internal.h`
- `dev/src/pa14_lowir_object_init.cpp`
- `dev/src/pa14_lowir_program.cpp`
- `dev/src/pa14_lowir_program_io.cpp`
- `dev/src/pa14_lowir_rtti.cpp`
- `dev/src/pa14_lowir_support.cpp`
- `dev/src/pa14_lowir_throw.cpp`
- `dev/src/pa14_lowir_value_addr.cpp`
- `dev/src/pa14_lowir_value_expr.cpp`

Recent non-PA25 cleanup to inspect for earlier-stage regression risk:

- `dev/src/ctrlexpr_support.cpp`
- `dev/src/pptoken_lib.cpp`

Performance risks to inspect:

- Repeated full AST or declaration walks during lambda capture analysis,
  initializer-list recognition, RTTI/typeinfo emission, function ordering, and
  template deduction.
- Hot-path reconstruction of semantic facts from names or LowIR strings.
- Repeated emission or canonicalization of RTTI globals, closure helpers,
  initializer-list backing storage, exception helpers, and external runtime
  declarations.
- The PA3 control-expression timeout fix for memory/time behavior and for
  preserving the tokenizer/evaluator pipeline.

Ownership boundaries to inspect:

- PA25 implementation stays in `dev/` and `dev/src/`; assignment directories
  remain handouts, harnesses, refs, and documentation.
- Semantic facts for captures, initializer lists, RTTI, `typeid`, and
  `dynamic_cast` are represented in typed semantic/lowering state rather than
  downstream string recovery.
- Throw/catch lowering remains owned by `pa14_lowir_throw.cpp`; general value
  expression lowering should not duplicate exception lowering ownership.
- `std::initializer_list<T>` support recognizes the library type without
  replacing user-declared member functions needed by overload resolution.
- Closure objects lower through the ordinary record/method path and do not
  embed runtime payloads or interpreter substitutes.

File-audit issues to inspect:

- `dev/src/pa14_lowir_throw.cpp` is included in the frontend source set.
- No implementation fragments were moved into unchecked directories or hidden
  behind assignment fixtures, wrappers, generated payloads, or binary blobs.
- File-size and ownership warnings from the PA25 file audit are understood and
  either resolved or verified as warnings that do not hide skipped work.
- No fixture-specific gates, timeout workarounds, or bypasses of the file audit
  are present.

## Findings

1. Fixed blocker: PA25 expression identity for `typeid` comparison and
   `dynamic_cast` lowering was being recovered from formatted AST strings.
   `pa12_expr_nodes.cpp` checked whether operands started with
   `typeid-expression`, and LowIR lowering checked for `dynamic_cast` in
   `Node::token_text`. That made a semantic PA25 fact depend on presentation
   text.

2. No skipped compiler phases or fallback output path found. PA25 still runs
   preprocessing, tokenization, parsing, semantic analysis, and LowIR lowering
   through the existing `cppgm++ --emit-lowir` pipeline. The implementation does
   not shell out to refs, previous compiler stages, host compilers, template
   binaries, interpreters, VMs, trampolines, or embedded payloads.

3. Capturing lambdas, initializer lists, RTTI/typeid, `dynamic_cast`, and
   source exception lowering are owned by the expected compiler layers. Lambda
   captures become generated closure fields, initializer lists are typed library
   records with LowIR backing storage, RTTI is emitted from record/type
   structure, and throw/catch lowering is isolated in `pa14_lowir_throw.cpp`.

4. The PA3 timeout cleanup commit is an algorithmic fix, not a timeout bypass:
   control-expression output streams per logical line, and phase 1/2 combines
   trigraph replacement with line-splice deletion while preserving the real
   tokenizer/evaluator path.

5. File audit passes. The warnings identify legacy large headers/catch-all
   modules, duplicate blocks, and long AST/LowIR construction strings. The new
   `pa14_lowir_throw.cpp` file is included in the frontend source set, and no
   PA25 implementation was moved into unchecked paths.

6. Output ordering and generated-helper pruning use LowIR symbol-reference scans
   at write time. They were reviewed as performance/ownership risks. They are
   presentation reachability over emitted LowIR, not source semantic recovery or
   fixture-specific gates, and no full-suite walk or timeout workaround was
   found there.

## Changes Made

- Added typed PA25 expression metadata to `pa12::internal::Node`:
  `is_typeid_expression` and `is_dynamic_cast_expression`.
- Marked `typeid` nodes during parsing in `pa12_expr_primary.cpp`.
- Marked `dynamic_cast` nodes during cast-expression construction in
  `pa12_expr_nodes.cpp`.
- Replaced the `typeid` comparison and `dynamic_cast` lowering string checks in
  `pa12_expr_nodes.cpp`, `pa14_lowir_value_expr.cpp`, and
  `pa14_lowir_value_addr.cpp`.
- Updated `pa25/plan.md` with `Architecture Review` and
  `Final Architecture Review`.

## Validation

Completed during audit:

```sh
make test-pa25
make test-report-through-pa25
perl scripts/cppgm_file_audit.pl --stage pa25 --paths dev/src
```

Observed results:

- `make test-pa25`: pass, `44/44`
- `make test-report-through-pa25`: pass, `2345/2345`
- file audit: pass with 23 warnings, all warnings inspected as audit signals
