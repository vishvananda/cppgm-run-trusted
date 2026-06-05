# PA21 Audit

## Audit Plan

Audit target: PA21 full-stage `cppgm++ --emit-lowir -O0`, with regression
coverage through PA21.

Files and ownership boundaries to inspect:

- Assignment contract and evidence: `TESTING_AND_REFERENCES.md`,
  `pa21/README.md`, `pa21/plan.md`, PA21 spec/general tests, recent PA21
  commits, and the last full log under
  `/home/vishvananda/work/.ralph/trusted-gpt-5.5-xhigh/last-test.log`.
- Template semantic graph: `dev/src/pa12_internal.h`,
  `dev/src/pa12_model.cpp`, `dev/src/pa12_templates.cpp`,
  `dev/src/pa12_templates_arguments.cpp`,
  `dev/src/pa12_templates_common.cpp`,
  `dev/src/pa12_templates_functions.cpp`,
  `dev/src/pa12_templates_instances.cpp`,
  `dev/src/pa12_templates_lookup.cpp`,
  `dev/src/pa12_templates_validation.cpp`,
  `dev/src/pa12_types.cpp`, and
  `dev/src/pa12_types_parameters.cpp`.
- Parser/declaration integration: `dev/src/pa12_decls.cpp`,
  `dev/src/pa12_decl_variables.cpp`,
  `dev/src/pa12_decls_initializers.cpp`,
  `dev/src/pa12_decls_members.cpp`,
  `dev/src/pa12_records.cpp`, `dev/src/pa12_names.cpp`,
  `dev/src/pa12_static_assert.cpp`, and `dev/src/pa12_support.cpp`.
- Expression/substitution/pack behavior: `dev/src/pa12_expr.cpp`,
  `dev/src/pa12_expr_call_helpers.cpp`, `dev/src/pa12_expr_ids.cpp`,
  `dev/src/pa12_expr_nodes.cpp`, `dev/src/pa12_expr_packs.cpp`,
  `dev/src/pa12_expr_pointer.cpp`, and `dev/src/pa12_expr_semantics.cpp`.
- LowIR ownership and emission boundaries: `dev/src/pa14_lowir*.cpp`,
  especially `pa14_lowir_program.cpp`, `pa14_lowir_program_io.cpp`,
  `pa14_lowir_call.cpp`, `pa14_lowir_ctor_init.cpp`,
  `pa14_lowir_init.cpp`, `pa14_lowir_object_init.cpp`,
  `pa14_lowir_support.cpp`, `pa14_lowir_value_addr.cpp`, and
  `pa14_lowir_value_expr.cpp`.
- Build/source-set coverage: `dev/frontend_source_sets.mk`.

Performance risks to inspect:

- Partial-specialization matching and ordering for repeated full candidate
  scans, repeated substitution, excessive type formatting, and cache misses.
- Function/member-template instantiation paths for eager body instantiation,
  stale lookup contexts, and repeated full-suite walks.
- Expression pack propagation and dependent call handling for repeated vector
  copying or recomputing template argument packs in hot paths.
- LowIR program finalization for repeated full-program scans, name parsing, or
  recomputation of specialization ownership during emission.

Audit/cheating risks to inspect:

- No skipped compiler phases, dummy or minimal LowIR output paths, embedded
  payloads, template binaries, trampolines, interpreters, or host/reference
  compiler execution in the compiler implementation.
- No fixture-specific gates keyed by test names, source filenames, `.ref`
  files, literal test comments, source shape, or expected outputs.
- No timeout workarounds in compiler code in place of algorithmic fixes.
- No stringly semantic facts where the compiler should carry typed template
  entity, argument, owner, or declaration identity.
- No hidden implementation fragments, unchecked source-set moves, weakened
  file-audit checks, or file-size bypasses.

Validation to perform after fixes:

- `make test-report-through-pa21`
- `perl scripts/cppgm_file_audit.pl --stage pa21 --paths dev/src`
- `git status --short`

## Findings

- Blocker fixed: dependent qualified/template-id types were encoded as
  `TemplateParameter` names with textual markers such as `<>` and
  `<decltype>`. Partial-specialization matching, pack-name discovery, and
  deferred validation then recovered semantic facts by inspecting those names or
  formatted active specialization names.
- Blocker fixed: `pa14_lowir_program.cpp` had a static-member deferral helper
  that treated a namespace-owned binding with `::` in its name as a qualified
  member definition. Current PA12 declarations already resolve class-qualified
  static member definitions to class-owned bindings and mark them
  `is_static_member`, so LowIR should rely on binding ownership instead of name
  parsing.
- No skipped compiler phases, dummy/minimal LowIR generation, embedded payloads,
  interpreter/VM/trampoline paths, reference-binary calls, host compiler output
  substitution, fixture-specific gates, or timeout workarounds were found in
  the PA21 compiler implementation. The only timeout and `execvp` uses found are
  in the test runner harness, not in `cppgm++`.
- The PA21 source split is represented in `dev/frontend_source_sets.mk`. The
  file audit reports warnings for known large/duplicate legacy areas but no
  failing file-size, hidden-fragment, unchecked-path, or bypass issue.
- Performance review found no full-suite walks or repeated all-program
  rescans in the audited template paths. Partial specialization scans are over
  the registered candidate vectors for one primary template, with instantiated
  class/function/variable results cached by canonical typed-argument keys.

## Changes Made

- Added explicit dependent-typename metadata to PA11 `Type`:
  `is_dependent_typename`, `dependent_typename_qualified`,
  `dependent_typename_template_id`, and `dependent_typename_decltype`.
- Added PA11 helpers for creating dependent typename placeholder types and for
  testing whether a `TemplateParameter` is a real deducible template parameter.
- Updated dependent type parsing in `pa12_types.cpp` to preserve existing
  display spellings while carrying qualified/template-id/decltype facts in the
  new metadata.
- Updated pack-name discovery, function-template deduction, class
  partial-specialization matching, dependent call/member placeholders, and
  active-instantiation deferred validation to use typed metadata and
  template-argument dependency checks instead of substring checks.
- Registered class-template validation records with their synthetic dependent
  argument lists so validation-time deferral uses the same typed dependency
  path as ordinary instantiation.
- Kept non-deduced dependent typenames from rejecting function-template
  candidates during deduction; instantiated candidates still flow through
  ordinary conversion checks after other parameters deduce the real arguments.
- Marked dependent template-template instance arguments with the existing
  `dependent` bit instead of treating the literal fallback name
  `template_parameter` as the semantic fact.
- Removed LowIR name parsing for qualified static member deferral; LowIR now
  uses `Binding::is_static_member`.

## Validation

- `make build`: pass.
- Focused PA21 checks: pass
  `tests/general/300-explicit-type-arg-decltype-member-access.t`,
  `tests/general/400-partial-specialization-alias-pattern.t`,
  `tests/general/100-relative-qualified-partial-specialization.t`,
  `tests/general/200-template-template-parameter.t`,
  `tests/spec/300-dependent-super-member-template-chain.t`,
  `tests/general/300-dependent-hidden-friend-static-member-definition.t`,
  `tests/general/300-function-template-local-static-per-specialization.t`,
  `tests/general/300-static-constexpr-function-template-pointer-array.t`, and
  `tests/general/300-variable-template-static-assert-specialization-selection.t`.
- Regression checks after the first through-report rerun: pass
  `pa19/tests/general/100-function-template-dependent-alias-parameter-overloads.t`
  and
  `pa20/tests/general/401-constexpr-static-array-pointer-loop-increment.t`.
- `make test-report-through-pa21`: pass, 1621 / 1621.
- `perl scripts/cppgm_file_audit.pl --stage pa21 --paths dev/src`: pass with
  9 warnings and no failing file-audit issue.
