# PA10 Audit

## Audit Plan

- Contract and regression scope: compare the implementation against
  `pa10/README.md`, `pa10/plan.md`, `TESTING_AND_REFERENCES.md`, the current
  PA10 tests, and the previous-stage command surfaces that still share
  `dev/cppgm++.cpp`.
- Source files to inspect: `dev/cppgm++.cpp`,
  `dev/frontend_source_sets.mk`, `dev/src/pa10_ast.h`,
  `dev/src/pa10_internal.h`, `dev/src/pa10_support.cpp`,
  `dev/src/pa10_parser_internal.h`, `dev/src/pa10_parser.cpp`,
  `dev/src/pa10_decls.cpp`, `dev/src/pa10_types.cpp`, and
  `dev/src/pa10_expr.cpp`.
- Ownership boundaries: verify the driver only parses the PA10 command shape
  and delegates, PA10 owns AST nodes and parsing without recovering facts from
  dumped text, preprocessing/posttoken conversion stays in the existing shared
  pipeline, and no handout/test/reference path is used as implementation input.
- Skipped-work and substitute checks: search for shells to reference binaries
  or host compilers, fixture/source-shape gates, dummy output generation,
  embedded payloads, interpreter/VM/trampoline behavior, fallback success paths,
  and unsupported syntax accepted as opaque placeholders.
- Semantic-fact checks: inspect type/name tracking, declaration parsing,
  declarator parsing, and expression parsing for stringly facts, duplicate
  ownership, or downstream reparsing of AST dump lines where earlier parser
  state should carry the fact directly.
- Performance risks: inspect parser lookahead helpers such as declaration/type
  probes, template angle handling, balanced-token collection, initializer and
  expression loops, token splitting, and AST dumping for avoidable quadratic
  rescans, excessive token copying, repeated full-suite walks, or hot-path
  recomputation.
- File-audit issues: run
  `perl scripts/cppgm_file_audit.pl --stage pa10 --paths dev/src`, confirm PA10
  code lives in audited `dev/src` files listed in `dev/frontend_source_sets.mk`,
  and check for hidden implementation fragments or bypassed size checks.

## Findings

- The PA10 command path in `dev/cppgm++.cpp` delegates `--emit-ast` to the PA10
  module and rejects unsupported emit options.  The top-level future-mode and
  batch harness paths still report not-implemented status, but they are outside
  the PA10 `--emit-ast -o <outfile> <srcfile...>` surface and are not fallback
  success paths for AST emission.
- No PA10 source shells out to reference binaries, host compilers, interpreters,
  VMs, helper scripts, or test fixtures.  No embedded payload, copied runtime,
  trampoline, template binary, fixture filename gate, timeout workaround, dummy
  output path, or skipped preprocessing/tokenization/parser phase was found.
- Type-name ownership was too broad: `add_type_name` inserted every type name
  into every active scope.  That made namespace, class, template, and local
  typedef facts globally visible as a parser side effect.
- Several parser decisions recovered facts from AST dump strings, including
  declaration-specifier continuation, non-type template default handling,
  builtin function-style casts, qualified type-id disambiguation, and trailing
  return type labels.
- Removing global type leakage exposed two real parser fact gaps: qualified
  namespace template-ids such as `ns::andx<ns::box<T>, int>` needed namespace
  member lookup during angle parsing, and inherited typedef casts in qualified
  member function bodies needed class-owned member type facts.
- File audit passed but initially warned that `dev/src/pa10_internal.h` had a
  substantial header body.  The warning came from declaration volume rather than
  hidden implementation, but it was PA10-owned and was cleaned up.
- Performance review found no PA10 blocker.  Lookahead and balanced scans are
  bounded to the current declaration, template argument list, initializer,
  expression, or statement; AST dumping walks each parsed tree once; there is no
  repeated full-suite or full-translation-unit recomputation in hot paths.

## Changes Made

- Added explicit parser metadata to AST and declaration parse results for
  builtin type expressions, qualified type-ids, primary type names, non-CV type
  specifier progress, keyword-only specifier sequences, and qualified type-name
  facts.
- Reworked type-name ownership so normal declarations target the nearest
  non-template owning scope while template parameters remain in the template
  parameter scope.
- Added namespace fact tables for namespace definitions, aliases, reopened
  namespaces, inline namespaces, and using directives, plus qualified namespace
  template-name recognition during template angle parsing.
- Added class member type fact tracking, inherited base type imports, and
  one-shot type imports for qualified member function bodies and qualified
  return-type casts.
- Replaced AST-line inspections in declaration/type/expression parsing with
  structured parser metadata.
- Fixed template-template parameter keyword leaf construction so it uses the
  consumed keyword token source rather than the following token.
- Split the private parser class declaration into
  `dev/src/pa10_parser_internal.h`, removing the PA10 header-body file-audit
  warning without moving implementation out of audited `dev/src` files.

## Validation

- `make test-pa10` passes: 134/134 local PA10 tests and 0/0 course PA10 tests.
- `make test-report-through-pa10` passes: all tracked stages PA1 through PA10,
  489/489 tests.
- `perl scripts/cppgm_file_audit.pl --stage pa10 --paths dev/src` passes with
  only pre-existing `nsdecl`/`nsinit` warnings outside PA10.
