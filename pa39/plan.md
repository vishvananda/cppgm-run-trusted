# PA39 Inception Plan

## Active Checkpoint

```sh
make -C pa39 compare-cppgm++-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
```

The full compiler inception compare now passes. The last object-level blocker
was:

```text
object mismatch:
  obj/pa39/selfhost/shared/release/cy86_elf_object.o
  obj/pa39/inception/shared/release/cy86_elf_object.o
```

Disassembly was identical. The visible ELF difference was that the host-seeded
object emits the weak COMDAT data symbol
`std::integral_constant<bool, true>::value`, while the self-built compiler omits
that weak variable in the inception object. This was a reproducibility issue in
static template member/global emission, not a new PA39 feature.

A one-file compile of `dev/src/cy86_elf_object.cpp` reproduced the split:
`../dev/cppgm++` matches the canonical selfhost object and emits the symbol,
while `obj/pa39/bin/selfhost/cppgm++-self` matches the inception object and
omits it. The generated code remains identical; only unreferenced weak static
data differs.

## Owning Earlier Surface

PA39 adds no language feature. The fixed blocker belongs to the earlier PA14
global/static-member emission surface, with PA12 static member use analysis as a
supporting input. The self-built compiler and host-seeded compiler must make the
same demand decision for weak hosted static data members that are referenced by
the same source compile.

The concrete fix target is scalar `constexpr` static member emission. Such
members should remain deferred unless their storage is actually demanded;
emitting them from constant rvalue reads, associated records, or hosted inline
function materialization creates layer-dependent weak object contents.

The fix keeps scalar `constexpr` static member rvalue reads as constant-only
uses and avoids broad associated-function static-member materialization for the
same scalar constants. Address/lvalue use still demands real storage. The
focused `cy86_elf_object.cpp` probe and the canonical PA39 selfhost/inception
objects now match byte-for-byte, and a PA14 reducer covers the semantic surface.

The immediately preceding PA14 fixes remain part of this checkpoint:

- unresolved-template storage-copy fallback is restricted to same-record
  copy/move construction, so converting constructors are lowered semantically;
- hosted `std::__cxx11::basic_string<char>::size() const` is treated as an
  exported libstdc++ member, avoiding layer-dependent weak inline emission.
- unresolved class-member template placeholders are not reserved as concrete
  emitted overload symbols; only concrete member overloads and specializations
  consume PA14 LowIR names.
- catch-only cleanup scopes do not force extra call-protection EH wrappers,
  preserving PA24 catch-return lowering.
- bare rethrow now emits nested catch-body object cleanups before
  `__cxa_rethrow`, and catch cleanup landing pads advertise the full active
  outer catch set so rethrows are not retagged as catch-all.
- the PA37 inliner/canonicalizer preserves source order for ordinary LowIR
  functions and declarations, with stable object-key ordering only when object
  metadata is present.
- the PA37 inliner cap for ordinary callees is restored uniformly so internal
  helper binding does not create runaway self-built optimizer growth.
- a new PA36 reducer covers nested `std::vector<bool>` default construction and
  `assign`, matching the previous selfhost failure pattern without depending on
  PA39.

## Validation Plan

1. Regenerate the affected selfhost object through PA39 and confirm the
   previous `cy86_elf_object.o` mismatch is gone. Done.
2. Rerun the focused PA37 optimizer checkpoint and the first PA39 reproducibility
   compare before the full compiler compare. Done.

   ```sh
   make -C pa37 test CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++ CPPGM_SKIP_DEV_REBUILD=1
   make -C pa39 compare-pptoken-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
   make -C pa39 compare-cppgm++-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
   ```

3. Before returning, run all required checks. Done:

   ```sh
   perl scripts/cppgm_file_audit.pl --stage pa39 --paths dev/src
   make test-report-through-pa38
   make -C pa39 test-through-pa10 CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
   make -C pa39 compare-pptoken-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
   make -C pa39 compare-cppgm++-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
   ```
