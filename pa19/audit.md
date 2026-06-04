# PA19 Audit

## Audit Plan

Inspect the PA19 implementation against `pa19/README.md`, `pa19/plan.md`, the
PA19 local tests, and the PA18-to-PA19 source changes in the current history.

Files and ownership boundaries to review:

- `dev/cppgm++.cpp` and `dev/frontend_source_sets.mk`: driver mode remains the
  PA19 `--emit-lowir -O0 -o <outfile> <src...>` path, and new source files are
  linked only through the compiler frontend source set.
- PA12 semantic model files: `dev/src/pa12_internal.h`, `pa12_model.cpp`,
  `pa12_support.cpp`, `pa12_names.cpp`, `pa12_types.cpp`, `pa12_decls.cpp`,
  `pa12_decls_initializers.cpp`, `pa12_records.cpp`, `pa12_statements.cpp`,
  `pa12_expr.cpp`, `pa12_expr_ids.cpp`, `pa12_expr_nodes.cpp`, and
  `pa12_expr_semantics.cpp`. These should carry syntax-to-semantics ownership:
  typed template arguments, integral constant values, lookup, `static_assert`,
  initializer handling, and expression facts should be represented here rather
  than reconstructed downstream from strings.
- PA12 template files: `pa12_templates.cpp`,
  `pa12_templates_functions.cpp`, `pa12_templates_instances.cpp`, and
  `pa12_templates_validation.cpp`. These should own template parameters,
  type/value substitutions, pack collection/expansion, explicit specialization,
  stale-primary refresh, and concrete instantiation without fallback success
  paths.
- PA14 LowIR files: `dev/src/pa14_lowir*.cpp` and
  `dev/src/pa14_lowir_internal.h`. These should lower completed semantic
  declarations only, without interpreters, trampolines, templated binaries,
  embedded payloads, dummy globals/functions, or PA19-only output formats.

Performance risks to inspect:

- Template specialization lookup/keying must avoid repeated full-program scans
  in hot paths where maps or owned metadata are already available.
- Pack expansion and substitution should avoid avoidable quadratic copying over
  arguments, parameters, members, and bases.
- LowIR emission should not repeatedly rescan all declarations to rediscover
  template/static-member/RTTI facts that the semantic layer already owns.
- Constant-expression evaluation should reuse structured expression/type/value
  facts instead of reparsing strings or rewalking unrelated declarations.

File-audit and integrity risks to inspect:

- No implementation fragments should be hidden outside `dev/` or unchecked
  source lists.
- No tests, `.ref` files, harnesses, file-audit scripts, timeout knobs, or
  reference-binary wrappers should be edited to mask missing compiler behavior.
- New `dev/src/*.cpp` files must remain present in `dev/frontend_source_sets.mk`.

## Findings

- PA14 RTTI and LowIR symbol helpers reconstructed template specialization
  components by parsing formatted record names. This was a stringly downstream
  recovery of facts PA12 already owned as typed template arguments.
- `Parser::instantiate_member_function_templates` swallowed all
  `runtime_error` exceptions while eagerly materializing member definitions for
  completed class-template specializations. That was a fallback success path for
  real body-instantiation failures.
- PA12 carried duplicate helper implementations in the template and declaration
  split files. After moving those helpers to common ownership, the file audit
  exposed two oversized PA12 template functions that needed to be split rather
  than hidden behind the duplicate blocks.
- The first structured RTTI rewrite regressed earlier PA17/PA18 name spelling
  by using `pa11::describe_type` for ordinary records. The correct spelling for
  RTTI/template symbol components is the semantic record/enum name, not the
  presentation string with `class` or `struct` prefixes.

No skipped compiler phase, dummy output generator, interpreter/VM/trampoline,
templated-binary substitute, embedded payload, fixture-specific gate, timeout
workaround, reference-binary dependency, or file-audit bypass was found in the
PA19 compiler path.

## Changes Made

- Added structured template-instance argument metadata to PA11 record types and
  populated it from PA12 class-template instantiation.
- Reworked PA14 record symbol and RTTI name construction to consume typed record
  metadata instead of splitting template display strings.
- Removed the broad ignored exception in member function template
  instantiation, so required instantiation failures now propagate.
- Added `dev/src/pa12_templates_common.cpp` and
  `dev/src/pa12_decls_common.cpp` for shared PA12 helper ownership, and wired
  both into `dev/frontend_source_sets.mk`.
- Split `register_function_template` and `complete_template_arguments` helper
  paths into smaller PA12 member functions that satisfy the file-audit function
  size limits.

## Validation

- `make build` passed after the source-set and helper refactors.
- `make test-report ACTIVE_TEST_REPORT_PAS='pa19'` passed: 113/113 PA19 tests.
- Representative regression checks passed after fixing record/enum spelling:
  `make -C pa17 check TEST=tests/spec/300-inherited-virtual.t` and
  `make -C pa18 check TEST=tests/spec/300-template-static-object-member-definition.t`.
- `make test-report-through-pa19` passed: 1473/1473 tests.
- `perl scripts/cppgm_file_audit.pl --stage pa19 --paths dev/src` passed with
  only legacy warnings in pre-existing namespace/model/internal-header areas.
