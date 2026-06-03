# PA9 Implementation Plan

## Compiler Path

`cy86` will extend the existing staged compiler infrastructure.  Each source
file is run through the PA5 preprocessor and post-token conversion, then the
post-token streams are concatenated in command-line order and parsed as one
CY86 program.

The PA9 implementation will live in `dev/src` and be wired only into the
`cy86` tool.  `dev/cy86.cpp` should remain CLI glue: parse `-o`, accept the
existing optional `--target` argument, construct preprocessor options, and call
the PA9 support library.

## Ownership Boundaries

- `cy86_model`: CY86 typed model, opcode descriptors, register and operand
  metadata, literal byte conversion helpers.
- `cy86_parser`: conversion from preprocessed/post-tokenized input to CY86
  statements and operands, including label syntax.
- `cy86_x86`: semantic validation, statement layout, x86-64 instruction byte
  emission, and ELF image construction.
- `cy86_support`: public compile-to-file entry point and file permission helper.

The parser must not recover semantics from formatted output.  It should carry
literal source/type facts and operand forms in typed structures through semantic
analysis and lowering.

## Lowering Design

CY86 registers are backed directly by x86-64 registers:

- `sp` -> `rsp`
- `bp` -> `rbp`
- `x*` -> `r12*`
- `y*` -> `r13*`
- `z*` -> `r14*`
- `t*` -> `r15*`

The generated program is a single writable/executable/readable ELF load
segment starting at `0x400000`.  CY86 data statements and generated x86 code
share the same image stream so labels have real virtual addresses.  Code uses
absolute address loads for CY86 label immediates and jumps, keeping statement
sizes stable during layout.

Integer and syscall instructions use scratch x86 registers (`rax`, `r10`,
`r11`, and syscall ABI registers) and store results back to CY86 destinations.
Floating operations use x87 instructions and red-zone temporaries when an
operand cannot be used directly as x87 memory.  Literal/data statements and
`data8`/`data16`/`data32`/`data64` emit PA2 little-endian bytes with the
alignment and width conversion rules from the handout.

## Validation

Fast diagnosis uses:

```sh
make test-report ACTIVE_TEST_REPORT_PAS='pa9'
```

After meaningful parser, semantic, lowering, ELF, or shared preprocessor wiring
changes, run:

```sh
make test-report-through-pa9
```

Before completion, also run:

```sh
perl scripts/cppgm_file_audit.pl --stage pa9 --paths dev/src
```

Older-assignment regressions from the through report are blockers and must be
fixed before PA9 is considered complete.

## Architecture Review

The implemented PA9 path follows the staged compiler ownership boundary in this
plan.  `dev/cy86.cpp` is CLI glue: it accepts `-o`, source files, and the
optional `--target` argument, then builds preprocessor options and calls
`cy86::compile_to_file`.  The current PA9 backend emits native Linux x86-64;
`--target` is accepted for harness compatibility and is not used to select an
alternate lowering path.

`cy86_parser` preprocesses each translation unit with the PA5 pipeline,
collects checked post-tokens, drops per-file EOF tokens, concatenates the
streams in command-line order, and parses them into typed `Statement`,
`Operand`, `ImmediateValue`, and `MemoryAddress` objects.  It does not parse
from formatted output or recover facts from strings after the fact.

`cy86_model` owns opcode descriptors, CY86 register parsing, literal decoding,
literal width conversion, label immediate resolution, and literal alignment
facts.  Scalar literal statements carry fundamental-type alignment; string
literal statements carry byte alignment, matching the PA9 reference layout.

`cy86_x86` owns semantic validation, label collection, statement layout, x86-64
emission, and ELF construction.  It emits one writable/readable/executable ELF
load segment at `0x400000`, with CY86 labels assigned to real virtual addresses
inside the emitted image.  Instruction sizes are stable during the single layout
pass because label immediates, jumps, and calls are lowered through fixed-width
absolute loads.

The lowerer emits real x86-64 instruction bytes and data bytes.  It does not
shell out to a host compiler, execute reference binaries, embed generated
program payloads, use an interpreter/VM, or gate behavior on test filenames or
fixture contents.  Hot paths are linear in source tokens/statements, with small
constant descriptor lookups and bounded per-instruction emission.

## Final Architecture Review

The audit cleanup kept the original architecture and fixed the issues found
inside it rather than adding a fallback path.  Literal alignment is now a typed
model fact, so the lowerer no longer infers alignment from encoded byte length
and no longer over-aligns string literal arrays.  Memory-address validation now
allows non-label literal terms to be converted as 64-bit immediates, while
label addends retain the README-required integral validation.

No skipped phases, dummy outputs, runtime payload substitutes, test-specific
gates, timeout workarounds, file-audit bypasses, duplicated semantic ownership,
or PA9 performance blockers remain from the reviewed implementation.  The
remaining PA9 source layout matches the source-set wiring in
`dev/frontend_source_sets.mk`, and new regression coverage lives under
`cppgm.tests/course/pa9/`.
