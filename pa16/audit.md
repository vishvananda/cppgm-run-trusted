# PA16 Audit

## Audit Plan

Contract and regression scope:

- Re-read `TESTING_AND_REFERENCES.md`, `pa16/README.md`, `pa13/lowir.md`,
  `pa16/plan.md`, PA16 local tests under `pa16/tests/general/` and
  `pa16/tests/spec/`, and earlier through-stage tests covered by
  `make test-report-through-pa16`.
- Compare the PA16 implementation commit against the PA15 audit baseline so
  regressions in PA1-PA15 behavior are treated as blockers, not PA16-only
  cleanup.

Implementation files to inspect:

- Build/source-set boundary: `dev/frontend_source_sets.mk`.
- Shared PA11 class metadata touched by PA16:
  `dev/src/pa11_internal.h`, `dev/src/pa11_model.cpp`.
- PA12 semantic ownership: `dev/src/pa12_internal.h`,
  `dev/src/pa12_model.cpp`, `dev/src/pa12_decls.cpp`,
  `dev/src/pa12_decls_members.cpp`, `dev/src/pa12_expr.cpp`,
  `dev/src/pa12_expr_nodes.cpp`, `dev/src/pa12_expr_semantics.cpp`,
  `dev/src/pa12_names.cpp`, `dev/src/pa12_records.cpp`,
  `dev/src/pa12_statements.cpp`, `dev/src/pa12_support.cpp`, and
  `dev/src/pa12_types.cpp`.
- PA14 LowIR ownership: `dev/src/pa14_lowir_internal.h`,
  `dev/src/pa14_lowir.cpp`, `dev/src/pa14_lowir_call.cpp`,
  `dev/src/pa14_lowir_ctor_init.cpp`, `dev/src/pa14_lowir_expr.cpp`,
  `dev/src/pa14_lowir_init.cpp`, `dev/src/pa14_lowir_object_init.cpp`,
  `dev/src/pa14_lowir_program.cpp`, `dev/src/pa14_lowir_support.cpp`,
  `dev/src/pa14_lowir_value_addr.cpp`, and
  `dev/src/pa14_lowir_value_expr.cpp`.

Ownership boundaries to verify:

- PA12 must own typed facts for selected constructors, assignment operators,
  conversion operators, deleted/defaulted special members, object lifetime
  actions, overload resolution, and cleanup-worthy semantic nodes.
- PA14 must consume those typed facts to choose LowIR storage, indirect
  class-value parameters and returns, helper emission, temporary
  materialization, constructor/destructor action lowering, and cleanup scopes.
- No later LowIR path should recover semantic facts from formatted names,
  test filenames, emitted LowIR text, or source-shape probes.

Performance risks to inspect:

- Repeated full-record scans while synthesizing copy/move constructors and
  assignment operators.
- Repeated overload, ADL, base/member, or conversion-operator walks in hot
  expression paths.
- Repeated helper-emission or LowIR top-level scans that can grow quadratically
  with functions, records, temporaries, or cleanup actions.
- Avoidable copies of large semantic expression/action vectors while lowering
  class arguments, return slots, aggregate initialization, arrays, and
  new/delete loops.

Audit and cheating risks to inspect:

- Skipped phases, fallback success paths, dummy/minimal LowIR output, and
  placeholder helper bodies.
- Interpreter, VM, trampoline, template-binary, copied-runtime, embedded
  payload, host-compiler, reference-binary, or prior-solution substitutes.
- Test-specific gates, source-shape acceptance filters, timeout workarounds,
  and file-audit bypasses or hidden implementation fragments outside `dev/src`.
- Stringly semantic facts, duplicated ownership of class layout/lifetime facts,
  and downstream recomputation of facts that should be represented in PA12.

File-audit issues to inspect:

- Confirm every new `dev/src/*.cpp` file is listed in
  `dev/frontend_source_sets.mk`.
- Inspect large touched files near or above 1,000 lines
  (`pa12_decls.cpp`, `pa12_decls_members.cpp`, `pa12_expr_nodes.cpp`,
  `pa12_records.cpp`, `pa14_lowir.cpp`, `pa14_lowir_program.cpp`,
  `pa14_lowir_value_expr.cpp`) for oversized hidden fragments, misplaced
  PA16 behavior, or mechanical splits that obscure ownership.
- Run `perl scripts/cppgm_file_audit.pl --stage pa16 --paths dev/src` after
  cleanup and treat any issue as a blocker.

## Findings

1. PA12 generated special-member recursion guards were keyed by unqualified
   record-name strings such as `Box::copy`, `Box::move_assign`, and `Box::~`.
   Distinct same-named records in different scopes could collide, making
   semantic generation depend on display spelling instead of record identity.

2. PA12 deferred inline special-member body parsing had a fallback success path:
   if parsing a constructor, destructor, or `operator=` body failed, it could
   attach an empty `compound-statement` and keep compiling. That was dummy body
   generation for required compiler artifacts.

3. File audit reported a PA16 duplicate block in
   `dev/src/pa12_decls_members.cpp`: the constructor-member body parser
   duplicated the helper already used for pending constructor bodies.

4. File audit reported a PA16 complexity warning in
   `dev/src/pa12_expr_nodes.cpp` for `Parser::make_subscript_expr`, where
   builtin subscript handling and record fallback were nested together.

5. Mechanical audit searches found no PA16 implementation shellout to reference
   binaries, host compilers, prior solutions, template binaries, interpreters,
   VMs, trampolines, copied runtime payloads, test filenames, or `.ref`/`.my`
   fixtures to produce LowIR. The old `--batch-stdin` driver path reports
   `EXIT_NOT_IMPLEMENTED` for the test harness protocol and is not used to
   produce PA16 LowIR output.

6. The final file audit still reports historical warnings for
   `nsinit_internal.h`, `pa12_internal.h`, `pa14_lowir_internal.h`,
   `nsinit_model.cpp`/`nsdecl_model.cpp`, `nsinit_parser.cpp`/`nsdecl_parser.cpp`,
   and `pa11_model.cpp`/`nsinit_model.cpp`. These are warnings, the command
   exits 0, and they are outside the PA16 blocker cleanup found in this audit.

## Changes Made

- Replaced PA12 generated constructor, destructor, copy/move constructor, and
  copy/move assignment guard keys with canonical record identity keys. Aggregate
  constructor guards now include both record identity and arity.
- Removed the deferred special-member empty-body recovery path so parse failures
  now fail the compilation instead of emitting dummy bodies.
- Reused `parse_constructor_body_from_parameters` for the non-inline
  constructor-member path in `pa12_decls_members.cpp`.
- Split record `operator[]` and pointer-conversion fallback into
  `make_record_subscript_expr`, leaving `make_subscript_expr` focused on
  builtin array/pointer subscript selection.

## Validation

- Focused checks:
  - `make -C dev cppgm++`
  - `make -C pa16 check TEST=tests/general/400-class-pointer-conversion-builtin-subscript.t`
  - `make -C pa16 check TEST=tests/general/300-proxy-subscript-assignment.t`
  - `make -C pa16 check TEST=tests/general/200-ref-qualified-call-operator.t`
  - `make -C pa16 check TEST=tests/general/300-local-default-ctor-return-copy.t`
  - `make -C pa16 check TEST=tests/spec/200-out-of-class-defaulted-special-members.t`
  - `make -C pa16 check TEST=tests/general/100-user-copy-constructor.t`
  - `make -C pa16 check TEST=tests/general/100-user-operator-assign.t`
  - `make -C pa16 check TEST=tests/general/300-destructor-alias-member-call.t`
  - `make -C pa16 check TEST=tests/general/200-out-of-class-special-members.t`
- Ad hoc same-name namespace copy/default special-member collision case:
  `dev/cppgm++ --emit-lowir -O0` exited 0 and emitted distinct helpers for
  `a::Box` and `b::Box`.
- Required through-stage test:
  `make test-report-through-pa16` passed with
  `ALL TESTS PASSED SUCCESSFULLY! (1143 / 1143)`.
- Required file audit:
  `perl scripts/cppgm_file_audit.pl --stage pa16 --paths dev/src` passed
  with exit status 0.
