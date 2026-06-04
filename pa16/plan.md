# PA16 Implementation Plan

## Design Direction

PA16 extends the PA15 semantic AST and LowIR lowering path. The implementation
stays in `dev/src`, with PA12 owning typed semantic facts and PA14 owning LowIR
storage/calling-convention decisions. The lowering code must not rediscover
constructor, copy, move, or conversion semantics from formatted node text.

## Compiler Ownership

- PA12 parser/semantics:
  - represent direct class initialization as typed constructor calls when a
    constructor is selected, including default arguments.
  - synthesize and register the supported implicit/defaulted copy and move
    constructors and assignment operators on demand.
  - keep deleted special members in `deleted_functions_` and reject calls to
    them during overload resolution.
  - attach chosen constructor/operator bindings to semantic nodes through
    `direct_call`, not by relying on name or arity later.
  - keep constructor/destructor/member/base actions as the source of truth for
    object lifetime.

- PA14 LowIR lowering:
  - lower class value parameters and returns through explicit object storage.
  - materialize lvalue/xvalue/prvalue class arguments in caller-owned temporary
    slots, then pass the indirect address.
  - lower selected copy/move/default/member/base actions from their typed
    bindings, demanding helper emission only when used.
  - preserve PA15 cleanup registration and scope unwind cleanup behavior.

## Implementation Checkpoints

1. Keep defaulted in-class special members as usable inline semantic helpers,
   while preserving out-of-class `= default` as a declaration that must be
   defined separately.
2. Fix direct constructor initialization so cases like `S b(a)` and
   base-subobject initializers select the constructor overload using the actual
   argument list, derived-to-base reference binding, and stored defaults.
3. Add semantic synthesis for the common implicit copy/move constructors and
   copy/move assignment operators, including deleted cases required by PA16.
4. Teach LowIR lowering to use those selected helpers for class value transfer,
   class pass-by-value, and class return-by-value.
5. Extend object initialization and member/base initialization for delegating
   constructors and out-of-class constructor/destructor definitions.
6. Fill the remaining PA16 surfaces covered by the suite: ref-qualified member
   calls, ADL/operator paths, scalar/array new and delete, unions, conversion
   operators, and correct temporary cleanup scopes.

## Validation Plan

- Use focused `pa16` local checks or `make test-report ACTIVE_TEST_REPORT_PAS='pa16'`
  while diagnosing each compiler-surface checkpoint.
- After meaningful semantic or lowering changes, run
  `make test-report-through-pa16` from the repository root.
- Keep `perl scripts/cppgm_file_audit.pl --stage pa16 --paths dev/src` passing.
- Commit cohesive checkpoints only after the relevant scoped test set improves
  and older through-stage behavior is preserved.

## Current Focus

- 2026-06-04: PA16 implementation is complete for the required stage. The
  semantic path now preserves typed selections for special members, overloads,
  conversion operators, class value transfer, new/delete, and cleanup scopes.
- LowIR lowering is split by ownership:
  - core statement/function lowering remains in `pa14_lowir.cpp`.
  - value/address expression lowering lives in `pa14_lowir_value_addr.cpp` and
    `pa14_lowir_value_expr.cpp`.
  - aggregate/object initialization lives in `pa14_lowir_object_init.cpp`, with
    constructor/member initialization in `pa14_lowir_ctor_init.cpp`.
  - declaration-member parsing is split into `pa12_decls_members.cpp`.
- Validation completed with scoped PA15/PA16 reports, the required
  `make test-report-through-pa16`, and
  `perl scripts/cppgm_file_audit.pl --stage pa16 --paths dev/src`.
