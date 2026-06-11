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
