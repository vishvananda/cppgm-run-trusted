# PA33 Implementation Plan

## Contract

PA33 extends the PA32 host object path from "host-linkable" to "host ABI/runtime
compatible" for the tested x86_64 Linux C++ subset. The implementation remains
in `dev/` and reuses the existing parser, semantic model, LowIR lowering, and
PA31 host object writer.

## Design

- Keep ABI facts in typed semantic/lowering state. Symbol spelling decisions
  should come from `Binding`, `Type`, scope, template, and record layout facts,
  then be carried to object emission through existing `object=` metadata.
- Implement Itanium vtable/RTTI ownership in the LowIR record lowering layer:
  records with an out-of-line key function import their vtable/RTTI from the TU
  that defines the key function, while all-inline/no-key polymorphic records
  emit weak COMDAT definitions in each using TU.
- Preserve the course LowIR symbol names as internal handles, but attach host
  ABI object names for vtables, RTTI, VTTs, construction tables, thunks,
  constructors, destructors, and template/lambda functions that are externally
  visible to the host linker/runtime.
- Fix host object lowering gaps by extending the native object backend rather
  than weakening tests: imported data/function relocations, ABI argument/result
  classification, varargs builtins, and stack allocation should map to normal
  host ABI behavior.
- Fix EH/runtime behavior in the PA31 host object path: cleanup pads must resume
  or dispatch correctly, rethrow must preserve the active exception, typed
  catches must use host RTTI-compatible objects, and `noexcept` termination must
  call the host runtime instead of crashing.
- Lower `dynamic_cast` upcasts with typed record-layout facts: fixed base
  offsets for non-virtual bases and vtable virtual-base-offset loads for virtual
  bases. Reserve `__dynamic_cast` for downcasts and cross-casts that need the
  host RTTI walk.

## Ownership Boundaries

- Parser/semantic changes belong in `pa11`/`pa12` sources only when the current
  typed model is missing a fact such as ABI tags, inline namespace ownership,
  lambda context, dependent aliases, or builtin types.
- ABI spelling and metadata belong in `pa14_lowir_*` helpers and the existing
  ABI mangling support, not in `pa31_host_object_*`.
- ELF section, symbol binding, relocation, LSDA, and machine-code details belong
  in `pa31_host_object_*`.
- Tests added during this work, if needed, go under `cppgm.tests/course/pa33/`.

## Validation

- Use focused `make -C pa33 check TEST=...` and
  `make test-report ACTIVE_TEST_REPORT_PAS='pa33'` while diagnosing PA33-only
  failures.
- After semantic, lowering, object, or shared runtime changes, run
  `make test-report-through-pa33`.
- Keep `perl scripts/cppgm_file_audit.pl --stage pa33 --paths dev/src` passing.
- Keep large PA33 additions split by responsibility so ABI expression mangling,
  RTTI/vtable emission, and host object calls do not become catch-all modules.
- Commit cohesive checkpoints only after the scoped or through report is stable
  enough to make the commit useful for regression isolation.

## Architecture Review

The PA33 implementation is organized around the intended phase boundaries.
Typed declaration, template, builtin, and record facts remain in `pa11`/`pa12`;
ABI spelling and LowIR metadata are produced in `pa14_lowir*`; ELF sections,
relocations, call lowering, LSDA, and host machine code stay in
`pa31_host_object*`. The audit did not find reference-binary shell-outs,
fixture-name gates, skipped compiler phases, embedded runtime payloads, or host
compiler output used as compiler output.

Two ownership defects needed cleanup. First, vtable/RTTI ownership was checking
whether any out-of-line virtual member was defined in the TU, which could emit a
vtable from a TU that defined a later virtual but not the key function. The
selection now walks class `binding_order`, chooses the first eligible key
function declaration, and treats duplicate out-of-class definition bindings as
definitions of that same key only when owner, name, and function type match.
Second, `__builtin_alloca` was declared as a host object import for `malloc`,
which was a semantic substitute instead of stack allocation. It is now a typed
`stackalloc` LowIR operation, rejected by the older CY86 backend and lowered by
the host object backend with a 16-byte-aligned dynamic `rsp` decrement restored
by the normal frame epilogue.

The file-audit pass also caught that adding alloca code directly to
`FuncGen::emit_value_instruction` pushed the dispatcher over the function-size
limit. That lowering was split into `FuncGen::emit_stack_alloc`, preserving the
host-object ownership boundary and keeping the dispatcher below the audit cap.

## Final Architecture Review

The final PA33 shape keeps object facts explicit: vtable/RTTI decisions are made
from `Binding` and `Type` state before object emission; the object writer
receives concrete LowIR operations and metadata rather than reconstructing C++
semantics from strings. Host-only constructs added for PA33, including
`stackalloc` and varargs, are explicit IR surfaces with validation and backend
ownership instead of fallback imports.

Regression coverage was added under `cppgm.tests/course/pa33/` for both audit
findings: a cross-TU key-function test proves a TU defining only a later virtual
imports, rather than emits, the key-owned vtable/RTTI; an alloca test proves the
object does not import `malloc`. The required through-stage report and file
audit pass on the final source.
