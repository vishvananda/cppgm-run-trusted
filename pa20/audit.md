# PA20 Audit

## Audit Plan

Audit target: PA20 full-stage `cppgm++ --emit-lowir` implementation in
`dev/` and `dev/src/`, with PA1-PA20 through-test coverage as the regression
gate.

Primary implementation files to inspect:

- Semantic model and constexpr ownership:
  `dev/src/pa11_internal.h`, `dev/src/pa11_model.cpp`,
  `dev/src/pa12_internal.h`, `dev/src/pa12_constexpr.cpp`,
  `dev/src/pa12_constexpr_values.cpp`,
  `dev/src/pa12_decl_variables.cpp`, `dev/src/pa12_static_assert.cpp`,
  `dev/src/pa12_support.cpp`, and `dev/src/pa12_types.cpp`.
- Declaration, member, expression, statement, and template integration:
  `dev/src/pa12_decls.cpp`, `dev/src/pa12_decls_initializers.cpp`,
  `dev/src/pa12_decls_members.cpp`, `dev/src/pa12_expr.cpp`,
  `dev/src/pa12_expr_ids.cpp`, `dev/src/pa12_expr_semantics.cpp`,
  `dev/src/pa12_records.cpp`, `dev/src/pa12_statements.cpp`,
  `dev/src/pa12_templates.cpp`, `dev/src/pa12_templates_functions.cpp`,
  `dev/src/pa12_templates_instances.cpp`, and
  `dev/src/pa12_templates_validation.cpp`.
- LowIR constant-initialization consumption:
  `dev/src/pa14_lowir_internal.h`, `dev/src/pa14_lowir_ctor_init.cpp`,
  `dev/src/pa14_lowir_globals.cpp`, `dev/src/pa14_lowir_init.cpp`,
  `dev/src/pa14_lowir_program.cpp`, `dev/src/pa14_lowir_program_io.cpp`,
  `dev/src/pa14_lowir_support.cpp`, and
  `dev/src/pa14_lowir_value_addr.cpp`.
- Build/source-set boundary:
  `dev/frontend_source_sets.mk`.

Performance risks to inspect:

- Constant-evaluation recursion and loop guards must be deterministic semantic
  guards, not wall-clock timeout workarounds.
- Expression, declaration, and LowIR lowering paths must avoid repeated
  full-program walks, repeated overload/template scans on hot paths, and
  quadratic copying of object/array constant values.
- Global and local-static initialization should reuse stored typed constant
  facts rather than recomputing semantic evaluation during every lowering pass.

Ownership boundaries to inspect:

- Parser/AST code should only preserve syntax needed by existing semantic
  actions; PA20 constexpr behavior should live in semantic code.
- Semantic code should own typed constant values, literal-type checks,
  `constexpr` declaration validation, `static_assert`, template-argument, and
  ordinary constant-initialization facts.
- LowIR code should only consume semantic constant facts and local-static
  metadata; it must not recover facts from generated text, AST formatting, or
  source-shape probes.
- Newly added implementation files must remain in `dev/src` and be listed in
  `dev/frontend_source_sets.mk`.

File-audit issues to inspect:

- No hidden implementation fragments in unchecked paths, no stage-handout edits
  used as implementation, and no file-audit bypasses.
- Source and internal header sizes must stay within the configured audit
  thresholds, especially `pa12_constexpr.cpp`, `pa14_lowir_init.cpp`,
  `pa14_lowir_program.cpp`, `pa12_expr.cpp`, and `pa12_internal.h`.
- Function length, nesting, duplicate-block, suspicious shortcut, and include
  checks from `scripts/cppgm_file_audit.pl --stage pa20 --paths dev/src` must
  remain clean.

## Findings

- `static_assert` had fallback-success paths for non-constant conditions,
  including false non-dependent call-expression conditions. That could hide
  missing constexpr evaluation and allow invalid programs through PA20.
- Constant evaluation skipped failures in executed statements. In particular,
  local declarations or expression statements that failed to evaluate could be
  ignored when a later `return` produced a constant value.
- Address-of evaluation contained a record-object fabrication fallback. A
  failed operand could become an empty typed object, allowing member calls on
  invalid temporaries instead of rejecting the expression.
- The recursion/step guard was stored in each evaluation frame, so nested
  constexpr calls reset the budget. That made the guard ineffective for
  recursive call chains and loops that cross function boundaries.
- Constructor/default-initialization coverage was incomplete for constexpr
  objects, defaulted constructors, member/base/delegating initializer actions,
  and scalar declaration validation. Some required constant-initialization
  failures were not diagnosed at the semantic owner.
- Typed object and string-literal facts were weaker than the PA20 contract:
  nested braced aggregates did not inherit element/field type context, pointer
  casts could discard object identity, integral comparisons did not honor the
  operand type width/signedness, and prefixed string literals such as `L"ab"`
  were not recognized by the constexpr subscript path after strict
  `static_assert` validation exposed the gap.
- File audit found a fatal size issue after the semantic audit changes:
  `dev/src/pa12_constexpr.cpp` exceeded the 1500-line threshold. No hidden
  implementation path, reference-binary substitution, generated-payload
  trampoline, timeout workaround, or test-specific source gate was found.

## Changes Made

- Replaced the per-frame evaluator budget with an active semantic budget shared
  across nested constexpr calls, with deterministic step and depth guards.
- Added an invalid evaluation flow and propagated it through declarations,
  expression statements, returns, conditions, loops, for-init/iteration, and
  constructor/storage/member/base actions so executed non-constant work cannot
  be skipped.
- Removed the fabricated record address fallback. Address-of now succeeds only
  when the operand evaluates to an object value.
- Added typed zero/default value construction for scalars, pointers, arrays,
  and records, plus constexpr constructor/defaulted-constructor handling for
  member/base/delegating initialization and storage-copy actions.
- Tightened `static_assert` and constexpr scalar variable initialization so
  non-dependent expressions must actually evaluate as constants. References and
  pointers retain semantic object/pointer identity instead of relying only on
  scalar `Binding::has_constant`.
- Preserved object/pointer identity through pointer casts, added nested
  braced-init type propagation, added typed subscript/string-literal element
  evaluation, and used operand type width/signedness for integral comparisons.
- Fixed prefixed string-literal constexpr indexing by using the existing
  `AnalyzeStringLiteral` decoder instead of checking only tokens beginning
  with `"`.
- Split pure constexpr value helpers into
  `dev/src/pa12_constexpr_values.cpp` and added
  `pa12_constexpr_values` to `dev/frontend_source_sets.mk`, keeping all PA20
  implementation under checked `dev/src` ownership and bringing
  `dev/src/pa12_constexpr.cpp` back under the file-audit size cap.
- Added regression tests under `cppgm.tests/course/pa20/` for rejected member
  calls on invalid temporaries and rejected skipped declarations in constexpr
  functions.

## Validation

- `make build` passed.
- `make test-pa20` passed: PA20 60/60 and course/pa20 2/2.
- `make test-pa19 TEST_FILTER=100-wide-string-literal-constexpr` passed after
  the prefixed string-literal fix. The PA19 target harness ran its full local
  set and reported 113/113.
- `make test-report-through-pa20` passed: 1535/1535.
- `perl scripts/cppgm_file_audit.pl --stage pa20 --paths dev/src` passed.
