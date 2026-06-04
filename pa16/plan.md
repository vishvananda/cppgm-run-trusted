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

## Architecture Review

The PA16 implementation keeps the PA boundary described above:

- PA12 owns source-level semantic facts. Class records, constructor and
  destructor actions, default arguments, deleted/defaulted functions,
  ref-qualified functions, conversion operators, and selected overloads are
  represented through `Binding*`, `TypePtr`, `Node::direct_call`, and typed
  action nodes before LowIR lowering starts.
- PA14 consumes those facts. It decides storage and call ABI shape through
  `record_pass_by_address`, `record_return_by_address`, `lowir_parameter`,
  constructor/destructor lowering, temporary slots, cleanup scopes, and
  demand-driven helper emission in `ProgramLowerer`.
- Source-set ownership is explicit in `dev/frontend_source_sets.mk`; the PA16
  LowIR split files all remain under `dev/src` and are built only into
  `cppgm++`.

The audit found two architecture issues in the PA12 layer:

- Generated special-member guards used unqualified record-name strings as the
  recursion/deduplication key. That made semantic generation depend on display
  spelling and could collide for distinct same-named classes in different
  scopes. The guards now key by canonical record object identity, with
  aggregate constructor arity included where needed.
- Deferred inline constructor/destructor/assignment bodies could recover from a
  parse failure by emitting an empty compound body for special members. That was
  a fallback success path and could turn unsupported or malformed user code
  into dummy LowIR. Deferred body parsing now propagates failures.

The audit also cleaned up two implementation-structure risks:

- The non-inline constructor-member parser path duplicated the constructor body
  initialization parser. It now delegates to
  `parse_constructor_body_from_parameters`, keeping constructor initializer
  ownership in one PA12 helper.
- `make_subscript_expr` mixed builtin subscript selection with record
  `operator[]` and pointer-conversion probing in one deeply nested function.
  Record fallback now lives in `make_record_subscript_expr`, leaving the
  builtin array/pointer path direct and reducing file-audit complexity.

## Final Architecture Review

PA16 now has no known unresolved audit blockers. The implementation does not
shell out to host compilers, reference tools, prior solutions, template
binaries, interpreters, VMs, trampolines, or embedded payloads to produce
LowIR. Unsupported semantic cases fail through the normal error path instead
of succeeding with placeholder output.

Typed ownership remains clear after cleanup:

- PA12 chooses constructors, conversion operators, assignment operators, and
  deleted/defaulted special members, then records those choices on semantic
  nodes and bindings.
- PA14 lowers from those bindings and typed nodes, including indirect
  class-value parameters/returns, temporary materialization, copy/move helper
  demand, constructor/destructor actions, and scope cleanup.
- Remaining file-audit warnings are pre-existing header-weight or nsinit/nsdecl
  duplication warnings outside the PA16 cleanup surface; the required audit
  command exits successfully for PA16.
