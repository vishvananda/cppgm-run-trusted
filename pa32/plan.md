# PA32 implementation plan

## Contract

PA32 reuses the existing PA29 compile-mode pipeline and PA31 host object writer.
The increment is to make `cppgm++ -c` emit ordinary x86_64 Linux relocatable
objects that the host C++ driver can link with host-built objects, archives, and
shared libraries. The main ownership boundary stays:

- parsing and semantic facts in `pa12_*`
- LowIR naming/linkage metadata in `pa14_lowir_*`
- compile-mode orchestration in `pa29_toolchain.*`
- ELF relocation/object details in `pa31_host_object.*`

The object writer should consume typed metadata already produced by semantic
lowering. It should not infer C++ semantics from formatted LowIR names except as
a fallback for internal compiler symbols.

## Completed implementation

PA32 now emits host-linkable relocatable objects for the tested subset. The
completed work extends ABI symbol formation, template/member replay, native
LowIR metadata, object-file relocation emission, TLS wrappers, EH/LSDA data,
constructor/destructor entry points, lifecycle arrays, dense vtables with
adjustor thunks, and no-op generated constructor pruning.

The PA31 object writer is split by ownership boundary:

- `pa31_host_object.cpp` keeps symbol selection, instruction lowering, and the
  top-level object write orchestration.
- `pa31_host_object_elf.cpp` owns ELF section/table serialization.
- `pa31_host_object_globals.cpp` owns globals, TLS data, and TLS wrapper
  emission.
- `pa31_host_object_eh.cpp` owns LSDA and `.eh_frame` emission.
- `pa31_host_object_internal.h` shares the object-writer data model between
  those implementation modules.

The ABI/template support was also split so substitution-aware ABI encoding and
member-body replay helpers remain below the audit size limits while preserving
typed semantic ownership.

## Implementation approach

1. Preserve the PA29 source-to-LowIR path and keep PA32 compile mode on the
   native-lowering path.
2. Extend the semantic/LowIR metadata path so externally visible C++ entities
   carry host ABI `object=` names from binding/type facts. Prefer the existing
   PA12/PA14 ABI helpers and expand them where needed for the tested subset.
3. Keep C linkage as raw symbol names, and diagnose C-linkage overload and
   function/variable symbol collisions during declaration processing.
4. Make inline/template/header-emitted definitions linkable across translation
   units by emitting weak definitions with host-compatible section/group
   semantics in the ELF writer.
5. Add TLS-aware object emission for `storage=thread_local` globals and their
   wrapper/helper symbols, using normal host relocations/sections for the tested
   local-exec/import-export subset.
6. Fill missing native object emission operations only where the LowIR already
   represents real compiled behavior. Do not add interpreter, trampoline,
   fixture-gated, or host-compiler output substitutes.
7. For dependent class-template member definitions, keep the semantic owner as
   PA12 bindings and template declarations. Instantiate concrete member and
   member-template bodies by replaying function bodies under typed template
   substitutions, not by reparsing formatted LowIR names or matching tests.
8. Treat declaration attributes as syntax that can appear before ordinary
   decl-specifiers, so template registration sees the real `static`, `inline`,
   return type, and member declarator facts.
9. Keep dependent out-of-class member-template recognition bounded to the
   declarator being registered. Trailing-return `decltype(...)` expressions can
   contain qualified calls, but those calls must not reclassify an ordinary
   namespace-scope function template as a class member definition.
10. Preserve LowIR function ordering with typed binding facts. When a
    template-specialized value constructor and scalar member helpers are emitted
    from the same expression chain, final ordering should keep the scalar
    helper/member calls ahead of the constructor without suppressing any real
    inline definition.

## Architecture Review

The PA32 path is an in-process source-to-object pipeline. `cppgm++ -c` is
parsed by `dev/cppgm++.cpp`, routed through `pa29_toolchain.cpp`, lowered by
PA14 with `native_lowering`, parsed back as LowIR only as a temporary internal
handoff, and then written by `pa31::write_host_object`. No PA32 compile path
execs the host compiler, a reference binary, or an object-template helper.

The driver boundary intentionally still recognizes `.obj` as the PA29
implementation-defined LowIR object format for earlier separate-compile tests.
For PA32 host objects, compile mode now routes every non-`.obj` output name
through the host ELF writer, so the host-object decision is not limited to
`.o` filenames.

Semantic ownership remains in PA12 and PA14. PA12 records C linkage, inline
status, template substitutions, member-template owner facts, and function
specialization symbols on bindings/template declarations. PA14 turns those
typed facts into LowIR metadata such as `object=`, `binding=`, TLS storage,
roles, aliases, and function ordering. PA31 consumes that metadata to choose
raw ELF symbols, sections, relocations, COMDAT groups, TLS wrappers, LSDA, and
`.eh_frame`; it does not recover public C++ ABI facts from fixture names or
external tool output.

The main audit risks are bounded to real compiler surfaces:

- `pa12_templates_function_abi*` has substitution-heavy logic and duplicated
  value-argument cases, but it operates on PA12 template/type data rather than
  test strings.
- `pa14_lowir_function_order.cpp` still contains pre-existing serialized-LowIR
  symbol scans for ordering. The PA32 addition for value constructors is typed
  around `Binding` and `TypePtr` facts and does not introduce a fixture gate.
- `pa31_host_object_internal.h` is large because it shares the object-writer
  data model and x86 emitter declarations across the split ELF/global/EH
  modules. It is checked by file audit and not an unchecked implementation
  fragment.
- The minimal `dev/include/exception` and `dev/include/stdexcept` headers
  provide declarations and small source-level class definitions for the tested
  hosted exception subset; runtime behavior still comes from normal emitted C++
  objects and host runtime symbols.

## Final Architecture Review

The audit cleanup keeps the architecture aligned with PA32. Compile-mode
object selection now matches the PA32 contract for ordinary output names while
preserving the PA29 `.obj` LowIR compatibility surface needed by earlier
through-stage tests. The host object writer also handles incoming stack-passed
parameters in the tested System V subset, copying them from the caller frame
into the LowIR frame after the integer or SSE register budgets are exhausted.

No unresolved PA32 architecture blockers remain from this audit. Object-writer
cases outside the supported LowIR surface still fail with explicit diagnostics
rather than producing placeholder output or silently switching to another
execution strategy. The implemented PA32 path emits real ELF relocatable
objects, preserves PA12/PA14 ownership of semantic facts, and keeps ELF/TLS/EH
details isolated in the PA31 host-object modules.

## Validation

- `make test-pa3` passes after the `ctrlexpr` hot-path cleanup that the
  through-stage report exposed.
- `make test-pa5` passes after preserving `defined` behavior for
  identifier-like operator tokens in the shared control-expression path.
- `make test-pa32` passes: `pa32 tests: PASS (77/77)`,
  `pa32 course/pa32: PASS (0/0)`.
- `make test-report-through-pa32` passes:
  `ALL TESTS PASSED SUCCESSFULLY! (2757 / 2757)`.
- `perl scripts/cppgm_file_audit.pl --stage pa32 --paths dev/src` exits
  successfully with 28 warnings and no errors.
