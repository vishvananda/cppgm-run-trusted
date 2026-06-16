# PA36 Audit

## Audit Plan

Target: `pa36 full-stage`

Required checks:

- `make test-report-through-pa36`
- `perl scripts/cppgm_file_audit.pl --stage pa36 --paths dev/src`

Implementation footprint to inspect:

- `dev/src/pa11_hosted_layout.cpp`, `dev/src/pa11_model.cpp`, and
  `dev/src/pa11_internal.h` for hosted record layout ownership and value ABI
  classification that later PA14 call/object emission consumes.
- `dev/src/pa12_*` declaration, expression, template, type, and ABI files
  changed by the PA36 implementation, especially `pa12_decls*.cpp`,
  `pa12_expr_semantics*.cpp`, `pa12_templates*.cpp`,
  `pa12_templates_function_abi*.cpp`, `pa12_templates_typename*.cpp`,
  `pa12_records.cpp`, `pa12_statements.cpp`, and `pa12_internal.h`.
- `dev/src/pa14_lowir*.cpp` and `dev/src/pa14_lowir_internal.h` for demanded
  inline/header body ordering, initializer-list lowering, hosted stream calls,
  implicit lifecycle demand, object initialization, RTTI/EH references, and
  fallback paths that could silently skip required codegen.
- `dev/src/pa31_host_object*.cpp` and `dev/src/pa31_host_object_internal.h` for
  ELF symbol binding, relocation kind selection, weak/COMDAT ownership, local
  runtime helpers, and avoidance of copied object/runtime payloads.
- `dev/src/cy86_*`, `dev/src/lowir2cy86*`, and
  `dev/frontend_source_sets.mk` for shared IR/object-model changes that could
  regress earlier stages or hide PA36 logic outside audited source sets.
- `pa36/tests/link/*` and `cppgm.tests/course/pa36/` only as oracles and
  coverage guides; handout tests and reference files must not be weakened.

Performance risks to inspect:

- Demand-closure walks that may repeatedly rescan all bindings, all records, or
  all template instances for every emitted function.
- Template replay/substitution paths that copy large ASTs, type vectors, or
  statement lists repeatedly instead of caching per concrete binding.
- Hosted layout and ABI classification recomputed in hot call-lowering paths
  instead of memoized on typed record or binding state.
- Symbol lookup and relocation emission paths that perform repeated demangling,
  broad string searches, or full-object scans per relocation.
- Any timeout knobs or early-success exits that mask algorithmic problems.

Ownership boundaries to verify:

- Parser and PA12 own declaration suffix facts, asm labels, type facts,
  concrete template bindings, and member-body replay metadata.
- PA12/PA14 ABI helpers own symbol spelling from semantic `TypePtr` and
  `Binding` state; later object writers should not reconstruct semantic facts
  from raw strings.
- PA14 owns demand-driven body ordering and concrete LowIR emission for
  demanded inline/template/header definitions.
- PA31 owns ELF sections, relocations, weak/local symbol binding, EH tables, and
  object-file runtime helper section ownership.
- Tests remain under PA36 course/test locations when added; PA handout refs are
  not edited except through documented reference regeneration, which is not
  part of this audit.

File-audit issues to inspect:

- Current file audit passes but reports warnings for large helper/header
  ownership in `pa11_internal.h`, `pa12_internal.h`,
  `pa12_decls_virtual_helpers.cpp`, `pa12_expr_call_helpers.cpp`,
  `pa12_templates_registration_helpers.cpp`, `pa14_lowir_internal.h`, and
  `pa31_host_object_internal.h`.
- Shortcut-risk warnings in `pa12_statements.cpp` and `pa14_lowir_init.cpp`
  need review to confirm they are target text/data generation rather than
  embedded executable payloads or fixture substitutes.
- Duplication warnings in PA12 template ABI/substitution helpers and PA14/PA12
  support helpers need review for duplicated semantic ownership or downstream
  fact recovery.
- Existing warnings outside the PA36 implementation footprint should not be
  churned unless they hide a PA36 blocker.

## Findings

- Found a PA36 ABI ownership blocker in `dev/src/pa12_statements.cpp`: the
  hosted `std::operator<<` stream insertion deferral path hand-built the raw
  Itanium specialization name for character and character-pointer insertion.
  That duplicated ABI spelling outside the PA12 ABI helper layer and triggered a
  file-audit shortcut-risk warning.
- No reference-binary shell-outs, host compiler fallback generation paths,
  copied executable payloads, dummy/minimal object output paths, fixture-name
  gates, timeout workarounds, or PA36 test-name gates were found in `dev/src`.
- Reviewed hosted body deferral and PA14 demand closure. Non-root hosted bodies
  remain semantic-only until demanded; demanded concrete inline/template bodies
  route through typed bindings, recorded template arguments, and PA14 LowIR
  emission.
- Reviewed PA31 host object ownership. Function calls use call/PLT relocation
  paths, data references use object/global relocation paths, and weak/COMDAT
  ownership remains in the object writer rather than in parser/lowering code.
- Reviewed file-audit warnings. The remaining `pa14_lowir_init.cpp`
  shortcut-risk warning is compressed target LowIR construction, not an
  embedded payload or fixture substitute. Other remaining warnings are
  non-fatal broad historical ownership, complexity, and duplication warnings;
  the PA36-specific shortcut-risk warning in `pa12_statements.cpp` was removed.

## Changes Made

- Added `dev/src/pa12_statements_hosted.cpp` for hosted statement-level stream
  symbol ownership.
- Added `Parser::mark_hosted_stream_insertion_extern_template` and registered
  `pa12_statements_hosted` in `dev/frontend_source_sets.mk`.
- Replaced the raw hosted stream insertion mangled string with a call to
  `abi_function_template_specialization_symbol`, using the existing
  `TemplateDeclaration` and concrete `TemplateArgument` state recorded by PA12.
- Removed the hosted stream insertion ABI helper from `pa12_statements.cpp`,
  keeping that file under the PA36 file-audit size limit.
- Updated `pa36/plan.md` with `Architecture Review` and
  `Final Architecture Review`.

## Validation

- `make build` passed.
- `make -C pa36 check TEST=tests/link/700-hosted-ostream-char-sequence-runtime-smoke.t`
  passed.
- `make -C pa36 check TEST=tests/link/700-hosted-ostream-integer-chain-runtime-smoke.t`
  passed.
- `make -C pa36 check TEST=tests/link/700-hosted-ostream-char-sequence-parameter-runtime-smoke.t`
  passed.
- `make test-report-through-pa36` passed:
  `ALL TESTS PASSED SUCCESSFULLY! (3243 / 3243)`.
- `perl scripts/cppgm_file_audit.pl --stage pa36 --paths dev/src` passed with
  non-fatal warnings.
