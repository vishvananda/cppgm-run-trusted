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

## Validation

- `make test-report ACTIVE_TEST_REPORT_PAS='pa12 pa15 pa23 pa27 pa31 pa32'`
  passes, covering the affected ABI/template, constructor-wrapper, and
  object-writer paths.
- `make test-report-through-pa32` passes.
- `perl scripts/cppgm_file_audit.pl --stage pa32 --paths dev/src` exits
  successfully with warnings only.
