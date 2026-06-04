# PA20 Implementation Plan

## Scope

PA20 extends the existing `cppgm++ --emit-lowir` compiler in `dev/` and
`dev/src/`. The implementation must build on the PA11-PA19 semantic and LowIR
pipeline rather than adding a separate execution path. The handout, tests, and
references under `pa20/` remain fixtures.

## Design

- Add a typed constant-evaluation layer owned by the semantic model. Reuse it
  for `static_assert`, constexpr variables, non-type template arguments, and
  constant initialization instead of recovering facts from emitted LowIR or
  formatted AST text.
- Represent constant results as values tied to compiler types: integral/bool,
  floating, null/pointer/reference identities, arrays, and class objects with
  field slots. Preserve existing scalar `Binding::has_constant` behavior as a
  compatibility projection for earlier PA code.
- Evaluate constexpr calls by binding parameters in a constant-evaluation frame,
  interpreting the existing semantic statement/expression tree for the supported
  C++11 subset, and returning typed values. The evaluator should handle
  recursion with a depth/step guard for diagnostics, not as a timeout workaround.
- Evaluate constexpr constructors and member functions by constructing or
  receiving object values, applying member-initializer lists/default
  initialization, and making `.`, `[]`, reference, and pointer observations read
  from typed constant objects.
- Treat `noexcept(expr)` as a semantic expression whose constant result is based
  on the selected callable's unwind metadata and the supported expression shape.
- Feed constant initialization facts into existing LowIR lowering so globals and
  function-local statics use data initializers when possible, while dynamic
  local statics retain guard/check code.

## Ownership Boundaries

- Parser changes stay limited to preserving syntax needed by the existing AST
  and semantic actions.
- Semantic changes belong in `dev/src/pa12_*` and shared semantic model headers.
- LowIR changes belong in `dev/src/pa14_lowir_*` only where they consume typed
  constant facts or local-static initialization metadata.
- New source files, if any, must be added to `dev/frontend_source_sets.mk`.

## Validation

- Use `make test-report ACTIVE_TEST_REPORT_PAS='pa20'` for scoped diagnosis.
- After meaningful semantic or lowering changes, run
  `make test-report-through-pa20`.
- Run `perl scripts/cppgm_file_audit.pl --stage pa20 --paths dev/src` before
  completion.
- Older-stage regressions found by through checks are blockers and must be fixed
  before considering PA20 complete.

## Audit Refactor

- Keep the typed constexpr evaluator and LowIR behavior unchanged while moving
  oversized dispatch branches into focused helpers.
- Split large declaration, return-conversion, call-building, and global-lowering
  functions along existing parser/lowerer ownership boundaries.
- Re-run the file audit, rebuild `cppgm++`, and finish with
  `make test-report-through-pa20`.

## Architecture Review

PA20 is implemented in the existing semantic and LowIR pipeline. The semantic
owner is the PA12 layer: `ConstexprValue` carries typed scalar, pointer,
reference, array, and record-object facts; `pa12_constexpr.cpp` evaluates the
supported C++11 constexpr expression and statement subset; and
`pa12_decls_initializers.cpp`, `pa12_decl_variables.cpp`, and
`pa12_static_assert.cpp` enforce declaration and assertion constantness at the
point where the compiler still has semantic type and binding information.

The evaluator now has a shared semantic budget for nested calls, explicit
invalid-flow propagation, and constructor/default-initialization handling for
typed objects. Constant results are not recovered downstream from emitted text:
LowIR continues to consume stored semantic initializer facts and object
metadata. The only new source boundary is `pa12_constexpr_values.cpp`, which
contains pure constexpr value helpers and is listed in
`dev/frontend_source_sets.mk`; it does not move implementation outside the
checked `dev/src` ownership path.

The audit found and removed the main architecture risks: fallback-success
`static_assert` behavior, skipped executed constexpr failures, fabricated
record-address objects, per-call budget resets, incomplete constructor/default
object initialization, and prefixed string-literal recognition gaps. No
interpreter/VM substitute, reference-binary shellout, embedded earlier-IR
payload, test-specific gate, timeout workaround, or unchecked implementation
fragment was found.

## Final Architecture Review

Final PA20 ownership is coherent: parser nodes preserve syntax, PA12 owns
typed constant semantics and diagnostics, and PA14 only consumes semantic facts
for LowIR generation. The implementation changes are scoped to the PA12
constexpr/declaration/static-assert path plus one source-set entry for the
helper split.

The final validation gates are clean. `make test-report-through-pa20` passes
1535/1535 tests, and
`perl scripts/cppgm_file_audit.pl --stage pa20 --paths dev/src` exits 0. The
file-audit size blocker introduced during the audit was resolved by the checked
helper split rather than by weakening audit checks or moving code to an
unchecked path.
