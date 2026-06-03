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
