# PA8 Audit

## Audit Plan

- Instruction and test surface:
  - Re-read `TESTING_AND_REFERENCES.md`, `pa8/README.md`, `pa8/plan.md`,
    the PA8 local tests under `pa8/tests/`, and the PA8 implementation commit
    `ef1f02f`.
  - Check regressions through PA8 with the root report target, not only local
    PA8 tests.
- Files to inspect:
  - Driver/API/source-set wiring: `dev/nsinit.cpp`,
    `dev/src/nsinit_support.h`, `dev/src/nsinit_support.cpp`, and
    `dev/frontend_source_sets.mk`.
  - PA8 model and ownership boundaries: `dev/src/nsinit_internal.h`,
    `dev/src/nsinit_model.cpp`, `dev/src/nsinit_eval.cpp`,
    `dev/src/nsinit_parser.cpp`, and `dev/src/nsinit_image.cpp`.
  - Shared token support touched for PA8: `dev/src/posttoken_support.h` and
    `dev/src/posttoken_support.cpp`, with attention to PA1-PA7 behavior.
- Semantic and fallback risks to inspect:
  - Ensure PA8 executes preprocessing, token conversion, parsing, semantic
    analysis, linking, constant evaluation, relocation, and image writing
    without fallback success paths, dummy artifacts, or copied/interpreted
    substitutes.
  - Search for test-specific gates, source-shape special cases, hardcoded
    fixture names, reference-binary shell-outs, host compiler delegation,
    embedded payloads, and timeout workarounds.
  - Verify ill-formed but syntactically valid PA8 inputs fail through semantic
    checks rather than parser escape hatches.
- Ownership and representation boundaries to inspect:
  - Confirm AST/model objects have clear owner containers and downstream code
    does not recover semantic facts from display strings.
  - Check linked entity identity, declaration order, internal linkage,
    namespace ownership, reference binding, temporary lifetime, and string
    literal order are represented explicitly.
  - Check values, relocations, pointer/reference representations, array
    extents, function signatures, and cv/storage/function specifiers flow
    through typed state instead of duplicated stringly facts.
- Performance risks to inspect:
  - Look for avoidable quadratic scans in name lookup, linking, initializer
    lowering, image layout, and repeated type-size or expression-evaluation
    paths.
  - Check for repeated full-suite or whole-program walks inside per-token,
    per-declaration, or per-byte hot paths, excessive byte-vector copying, and
    recursive paths that can explode on nested declarators.
- File-audit risks to inspect:
  - Run the stage file audit after cleanup and check that PA8 implementation
    remains inside audited `dev/src` files.
  - Inspect for hidden implementation fragments, generated unchecked payloads,
    weakened audit checks, oversized source fragments, or source moved to
    unchecked paths.

## Findings

- No reference-binary shell-outs, host compiler delegation, interpreter/VM
  substitutes, template binary payloads, copied runtime images, timeout
  workarounds, hidden implementation fragments, or test-name/source-shape gates
  were found in the PA8 implementation path.
- Initializer lowering in `dev/src/nsinit_image.cpp` had fallback success
  paths: invalid pointer, reference, array, string-literal, and arithmetic
  initializers could be accepted and emitted as zero bytes instead of
  diagnosing.
- Fundamental conversion lowering did not canonicalize `bool` initialization
  and did not materialize floating-to-integral constants such as `int i = 2.0`
  according to the PA8 reference.
- `constexpr` variables were accepted without an initializer or with a
  nonconstant initializer, and `constexpr` object declarations did not carry
  the const/internal-linkage fact needed by the linker.
- `thread_local` was represented as the same storage enum as `static` and
  `extern`, so specifier order changed linkage behavior for declarations such
  as `static thread_local int x` and `extern thread_local int x`.
- Mock function stubs were given 4-byte image alignment.  The PA8 reference
  emits the four-byte stub without padding after one- and two-byte objects, so
  hidden binary comparisons could fail for cases such as `char c; int main()`.
- File audit warnings were inspected.  The warning on
  `dev/src/nsinit_internal.h` is from declarations/model types in the internal
  PA8 contract, not hidden implementation body.  The duplication warnings are
  the explicit PA8 fork of PA7 namespace-declaration scaffolding kept inside
  audited `dev/src` ownership so PA7 behavior remains unchanged.

## Changes Made

- Added typed initializer compatibility checks in `dev/src/nsinit_image.cpp`:
  reference cv-qualification checks, rvalue-reference rejection for reachable
  PA8 expressions, pointer pointee/function/void/string-literal compatibility,
  null pointer constant handling, invalid scalar-to-array rejection, and
  invalid string-to-`char*` rejection.
- Added `InitPlan::constant` to separate well-formed nonconstant initialization
  from constant initialization and to reject nonconstant `constexpr`
  initializers.
- Canonicalized bool output to `0` or `1` and materialized constant
  floating-to-integral and integral-to-floating conversions.
- Split `thread_local` into an explicit entity/specifier bit instead of using
  it as linkage storage, preserving `static` and `extern` meaning regardless
  of specifier order.
- Made `constexpr` variables require initializers and apply const object type
  semantics for PA8 linkage/type checks.
- Matched PA8 reference image placement for function stubs while keeping the
  required four-byte `fun\0` representation.
- Added PA8 course regressions under `cppgm.tests/course/pa8/` for bool and
  floating initialization, function placement after `char`, invalid pointer,
  string pointer, reference cv, array scalar, constexpr nonconstant, and
  `static thread_local` linkage cases.

## Validation

- `perl pa8/scripts/run_all_tests.pl dev/nsinit my cppgm.tests/course/pa8`
  passed for the new course tests.
- `perl pa8/scripts/compare_results.pl ref my cppgm.tests/course/pa8`
  passed: `PASS (8/8)`.
- `make test-pa8` passed: PA8 local `41/41`, PA8 course `8/8`.
- `make test-report-through-pa8` passed:
  `ALL TESTS PASSED SUCCESSFULLY! (342 / 342)`.
- `perl scripts/cppgm_file_audit.pl --stage pa8 --paths dev/src` exited 0:
  file audit passed for PA8 with three inspected warnings.
