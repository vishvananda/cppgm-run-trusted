# PA29 Implementation Plan

## Contract

PA29 extends the existing cumulative `cppgm++` binary. The compiler must:

- compile one source file per `-c` invocation into an object-like file
- link object-like files and source inputs into one executable
- make direct source linking behave like separate compile plus link
- support mixed source/object links
- pass `-I`, `-L`, `-l`, and `--target` through the appropriate driver layer
- preserve the PA10-PA28 emit modes and through-stage behavior

## Design

The PA29 object format is compiler-owned LowIR text with a short magic header.
Compile mode lowers exactly one translation unit through the existing
preprocess, parse, semantic, and LowIR pipeline and writes that object file.
Link mode reads any compiler-owned object files, compiles source inputs to
temporary LowIR objects, concatenates those LowIR translation units in argument
order, and sends the combined LowIR to the existing PA28 native backend.

This keeps the semantic ownership boundary intact:

- `dev/cppgm++.cpp` parses driver arguments and dispatches modes.
- PA29 support code owns object-file classification, temporary object paths,
  library search, and final link materialization.
- PA14 continues to own source-to-LowIR lowering.
- PA28 `lowir2native` continues to own native executable generation.

Include search paths are real preprocessor state, not source-text rewriting.
`-I` entries are stored in `preproc::Options` and searched after the including
file's directory and before the current working directory fallback.

For `-L`/`-l`, link mode resolves `lib<name>.o` in the recorded library search
paths. The supported PA29 interop target is simple ELF64 x86-64 relocatable
helper objects emitted by the harness host C/C++ compiler. The linker support
must be generic over object symbols and relocations used by those helpers; it
must not special-case fixture names or expected outputs.

## Implemented Support

Object linking keeps each translation unit semantic pass independent and merges
only LowIR/object facts at the PA29 boundary. Internal symbols are renamed per
object, global declarations and definitions are coalesced, duplicate strong
definitions are rejected, and namespace-scope init/fini entrypoints are
synthesized across the linked program.

Native output reuses the PA28 backend with an explicit list of external ELF
relocatable objects. The ELF loader imports helper-object symbols, sections, and
relocations into the existing x86-64 image builder so PA29 libraries participate
in normal symbol resolution instead of being treated as source fixtures.

The driver owns mode selection and option routing. Compile mode requires one
source input and writes one compiler object; link mode accepts any mixture of
source files, compiler objects, and `-l` helper objects. Earlier emit modes are
preserved and bypass PA29 linking.

Runtime correctness needed by the PA29 source-driven tests stays in the
existing compiler layers:

- exception lowering now represents catch-all, typed catch, cleanup-only, and
  nested catch control flow directly in LowIR and the CY86 backend
- catch-by-value materialization, constructor function-try-block rethrow, and
  constructor member unwind cleanup are handled by PA14 lowering
- global string-literal array initialization emits static data rather than a
  runtime pointer store
- `__int128_t` and `__uint128_t` are real fundamental scalar types through
  semantic analysis, ABI classification, LowIR, two-register call/return
  lowering, comparisons, and helper-backed multiply/divide/modulo/shift paths
- the PA29 `<exception>` shim and ABI support labels cover the subset required
  by existing exception dispatch tests

## Architecture Review

The implemented PA29 driver keeps the stage boundary in `dev/cppgm++.cpp` and
`dev/src/pa29_toolchain.cpp`. `cppgm++` parses the practical driver options and
constructs `pa29::Options`; the PA29 layer validates the supported native
target, compiles source inputs through `pa14::emit_lowir` with native lowering
enabled, and leaves earlier `--emit-*` modes on their existing paths.

Source inputs are still compiled as independent translation units. Link mode
does not concatenate source text or reuse parser state: it compiles source
inputs to temporary compiler-owned LowIR objects, parses explicit object inputs,
renames object-local symbols and per-object lifecycle hooks, and then merges
only LowIR declarations, definitions, aliases, and init/fini roles. Strong
duplicate LowIR definitions fail during this merge.

Include paths are owned by `preproc::Options`. For PA29 driver invocations,
user `-I` paths are searched before the compiler shim include paths, while the
preprocessor still searches the including file's directory first and the current
working directory fallback last. This keeps include behavior in the
preprocessor instead of rewriting source text in the driver.

External helper libraries are resolved by `-L`/`-l` in `pa29_toolchain.cpp` and
passed to `lowir2native` as external ELF relocatable object paths. The native
backend loads those objects in `cy86_elf_object.cpp`, imports allocated
sections, symbols, and RELA relocations, reserves external labels before source
layout, rejects duplicate external global definitions, applies relocations, and
emits call thunks so helper C ABI functions participate in normal native symbol
resolution. There is no host-linker delegation, reference-binary callout,
template executable, VM, or embedded output payload in the implementation path.

The hot paths are bounded by per-object and per-symbol maps/sets rather than
repeated full-suite or source-shape scans. Object merge performs one parse and
one rename/update pass per input object. ELF import performs one section pass,
one symbol-table pass, and one relocation pass per helper object.

## Final Architecture Review

The audit confirmed that PA29 is implemented as a real extension of the
existing compiler pipeline rather than a replacement path. The final driver
architecture is:

- compile mode: `cppgm++ -c` validates the target and writes one compiler-owned
  LowIR object generated by the normal preprocessor, parser, semantic, and PA14
  lowering pipeline
- direct source link: each source input is compiled independently to a temporary
  LowIR object and then merged through the same object linker used by explicit
  separate compilation
- mixed link: explicit compiler objects and newly compiled source objects are
  merged together before native lowering
- library link: `-l` helper objects are imported as ELF64 relocatables by the
  native backend, with duplicate external definitions rejected before final
  image layout

The audit cleanup tightened three architecture edges: PA29 user include paths
now have the expected precedence over internal shim headers, unsupported targets
are rejected in compile mode as well as link mode, and duplicate helper-object
symbols can no longer silently overwrite each other in the native label table.
The source-set wiring includes all new `dev/src/*.cpp` files, and the file audit
continues to pass without moving implementation into unchecked paths.

## Validation

Fast iteration:

```sh
make test-report ACTIVE_TEST_REPORT_PAS='pa29'
```

Required completion checks:

```sh
make test-report-through-pa29
perl scripts/cppgm_file_audit.pl --stage pa29 --paths dev/src
git status --short
```

After stable checkpoints, commit cohesive progress. If the through report finds
an older-stage regression, fix that before continuing PA29 feature work.
