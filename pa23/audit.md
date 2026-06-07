# PA23 Audit

## Audit Plan

Audit target: `pa23 full-stage` for `cppgm++ --emit-lowir -O0`.

Implementation files to inspect:

- Template semantic state and substitution: `dev/src/pa12_templates*.cpp`,
  `dev/src/pa12_templates*_support.h`, and template fields in
  `dev/src/pa12_internal.h` / `dev/src/pa12_model.cpp`.
- Expression replay and constant-expression integration:
  `dev/src/pa12_expr*.cpp`, `dev/src/pa12_constexpr.cpp`,
  `dev/src/pa12_static_assert.cpp`, and related declaration parsing paths.
- Declaration, record, lookup, and type ownership:
  `dev/src/pa12_decls*.cpp`, `dev/src/pa12_records.cpp`,
  `dev/src/pa12_names.cpp`, and `dev/src/pa12_types*.cpp`.
- LowIR lowering and symbol emission affected by templates:
  `dev/src/pa14_lowir*.cpp`.
- New source-set wiring and file-audit coverage:
  `dev/frontend_source_sets.mk` and all new `dev/src/*.cpp` splits from the
  PA23 implementation commit.
- Incidental shared changes in `dev/src/pa11_*`, `dev/src/macro_support.cpp`,
  and `dev/src/lowir2cy86_model.cpp` for cross-stage regressions.

Performance risks to inspect:

- Recursive template completion and replay guards that might hide missing work
  or convert real completion into silent success.
- Repeated full template/record/function scans during overload resolution,
  partial-specialization matching, class completion, and LowIR inline ordering.
- Avoidable copying of token spans, template argument packs, lowered globals,
  and function bodies on hot paths.
- Quadratic candidate matching in member-template, constructor-template, and
  partial-ordering paths.

Ownership and semantic-boundary risks to inspect:

- Stringly recovery of template facts from formatted names instead of typed
  `TemplateArgument`, dependent-owner, or expression-span state.
- Duplicate ownership of instantiated functions, class specializations,
  member templates, variable templates, and out-of-class definitions.
- Downstream LowIR or symbol code reconstructing semantic facts that should
  already be represented by PA12 semantic objects.
- SFINAE paths that turn hard errors into candidate removal outside immediate
  template contexts, or paths that suppress candidate diagnostics by returning
  placeholder success.

File-audit issues to inspect:

- New large source splits are listed in `dev/frontend_source_sets.mk` and remain
  under `dev/src`.
- No implementation fragments were moved to unchecked paths, generated blobs,
  embedded payloads, copied runtimes, trampoline binaries, VM/interpreter
  substitutes, or test fixture gates.
- No weakened audit scripts, hidden file-size bypasses, or local harness
  shortcuts were added.

## Findings

- No skipped compiler phase, fallback success path, dummy/minimal LowIR output,
  reference-binary shell-out, VM/interpreter/trampoline, embedded payload,
  copied runtime, timeout workaround, or PA23 fixture/test-name gate was found
  in `dev/src` or `dev/cppgm++.cpp`. The implementation remains in the
  PA12 semantic and PA14 LowIR pipeline.
- New PA23 source splits are wired through `dev/frontend_source_sets.mk`; no
  added `dev/src/*.cpp` implementation file is outside the `cppgm++` source
  set.
- File audit initially passed before edits, but flagged PA23-era duplication
  involving initializer and overload helper code. Review found duplicated
  local `same_template_specialization_record` helpers in
  `dev/src/pa12_decls_initializers.cpp` and
  `dev/src/pa12_expr_call_helpers.cpp`; those helpers compared instance
  argument types by pointer and did not preserve the full typed value/owner
  argument state.
- Expanding the compressed PA23 initializer and overload helper functions made
  two file-audit fatal function-size issues visible during cleanup:
  `Parser::apply_record_variable_initializer` and
  `Parser::select_overload_expr` exceeded the audit line limit. That was a
  cleanup blocker, not a future-work item.
- The first shared comparison version was too broad because it stripped cv and
  accepted any identical stripped type. The through-stage report caught this as
  a PA22 regression in
  `pa22/tests/general/200-ambiguous-cv-pointer-partial-ordering-bad.t`, where
  cv-symmetric function-template partial ordering incorrectly became
  non-ambiguous.
- Remaining file-audit warnings after cleanup are non-fatal pre-existing or
  broad-division warnings. They do not indicate unchecked implementation
  movement, bypasses, hidden payloads, or required PA23 behavior left undone.

## Changes Made

- Added a shared `same_template_specialization_record` declaration in
  `dev/src/pa12_expr_semantics_support.h` and implemented recursive typed
  comparison in `dev/src/pa12_expr_semantics.cpp` for record template
  specializations, including type, value, template, and pack instance
  arguments.
- Removed the duplicate weaker specialization comparison helpers from
  `dev/src/pa12_decls_initializers.cpp` and
  `dev/src/pa12_expr_call_helpers.cpp`.
- Constrained the shared comparison to record template specializations only, so
  function-template signature checks preserve cv distinctions such as
  `const T*` versus `volatile T*`.
- Split oversized helper logic into named PA12 methods:
  `demand_empty_record_conversion_bodies`,
  `record_copy_move_initializer_blocked`,
  `replacement_function_template_definition`, and
  `instantiate_target_overload_candidate`.
- Updated `pa23/plan.md` with `Architecture Review` and
  `Final Architecture Review` sections grounded in the current PA12/PA14
  implementation.

## Validation

- `make build` passed after cleanup.
- Targeted regression check passed:
  `make -C pa22 check TEST=tests/general/200-ambiguous-cv-pointer-partial-ordering-bad.t`.
- Required tests passed:
  `make test-report-through-pa23` (`2201 / 2201`).
- Required file audit passed:
  `perl scripts/cppgm_file_audit.pl --stage pa23 --paths dev/src`.
- `git diff --check` passed.
- Implementation shortcut/reference search over `dev/src` and `dev/cppgm++.cpp`
  found no subprocess/reference/test-path/time-limit coupling.
