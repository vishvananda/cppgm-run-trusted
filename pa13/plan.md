# PA13 Implementation Plan

## Scope

Implement `lowir2cy86` as the PA13 LowIR-to-CY86 adapter.  The tool remains a
backend adapter over LowIR text: it parses one or more LowIR input files,
validates the PA13 structural/type/metadata contract, and emits deterministic
PA9 CY86 source text.  It does not lower C++ source, call reference binaries,
emit native objects, or add a second compiler path.

## Design

- Keep `dev/lowir2cy86.cpp` as command-line glue for `-o <outfile> <srcfile>...`.
- Add a small LowIR implementation under `dev/src/`:
  - a typed LowIR model for top-level declarations/definitions, types,
    metadata, values, blocks, slots, and instructions;
  - a text lexer/parser for the PA13 grammar, including metadata and optional
    debug suffixes;
  - a validator for duplicate symbols, object aliases, function-local names,
    block terminators, target existence, metadata values, call signatures, and
    call-boundary parameter rules;
  - a CY86 emitter that owns symbol spelling, stack layout, startup hooks,
    global data layout, function prologues/epilogues, calls, control flow,
    scalar operations, memory operations, object copy/zeroing, atomics, and the
    simplified exception handler stack used by the PA13 tests.
- Wire new `dev/src/*.cpp` files into `FRONTEND_OBJ_BASENAMES_lowir2cy86` only,
  reusing PA9 CY86 source-language conventions but not the PA9 native emitter.

## Validation Strategy

- During parser/emitter work, use the scoped report:
  `make test-report ACTIVE_TEST_REPORT_PAS='pa13'`.
- After meaningful parser, validation, lowering, or shared infrastructure
  changes, run the required through check:
  `make test-report-through-pa13`.
- Before handoff, also run:
  `perl scripts/cppgm_file_audit.pl --stage pa13 --paths dev/src`.
- Keep older-assignment regressions as blockers and leave the worktree clean
  with cohesive progress committed.

## Architecture Review

The PA13 implementation is a self-contained `lowir2cy86` adapter.  The driver in
`dev/lowir2cy86.cpp` parses the `-o <outfile> <srcfile>...` surface, supports the
test harness batch mode by running the same compile path per request, and reports
exceptions as failed tool exits.  It does not call host compilers, reference
binaries, previous-stage tools, or alternate generators to produce CY86 output.

The editable implementation is split under `dev/src/`:

- `lowir2cy86_model.cpp` and `lowir2cy86.h` own the LowIR program model, type
  model, metadata, values, blocks, instructions, globals, aliases, and stack
  layout fields.
- `lowir2cy86_parser.cpp` lexes and parses all input files into one `Program`
  in command-line order.  The parser accepts PA13 metadata and debug suffixes
  as text; it does not recover semantics from fixture names or reference output.
- `lowir2cy86_validate.cpp` owns duplicate detection, top-level maps,
  function-local maps, block target checks, metadata validation, role
  resolution, TLS wrapper checks, temporary typing, and stack layout.
- `lowir2cy86_emit.cpp` consumes the validated/layouted program and owns CY86
  symbol spelling, startup/init/fini dispatch, function prologues/epilogues,
  stack-address calculations, calls, globals, object copies/zeroing, atomics,
  conversions, and the simplified exception-handler stack used by the PA13
  tests.
- `lowir2cy86_support.cpp` is only the parse/validate/emit/write bridge.

The implementation uses maps and sets for top-level symbols, locals, block
labels, aliases, roles, temporaries, slots, and parameters, so validation and
emission do not repeatedly rescan whole programs for hot-path lookups.  The
emitter still emits object copies and zeroing as straight-line CY86, which is
appropriate for the small fixed spans in PA13 LowIR and now handles non-qword
tails exactly.

The current checked PA13 oracle treats the general `f80`
direct-call/global/arithmetic fixtures as negative cases while accepting f80
conversion fixtures.  The implementation therefore preserves f80 storage for
the accepted conversion paths and keeps the current oracle-compatible rejection
of those general f80 surfaces.

## Final Architecture Review

The audit kept the three-layer ownership boundary intact: parsing builds owned
LowIR data, validation records and checks semantic facts before layout, and
emission relies on the validated model instead of raw source text.  Cleanup
strengthened that boundary by moving role ownership checks, call-signature
metadata restrictions, and bulk-memory operand validation into
`lowir2cy86_validate.cpp`.

The CY86 emitter remains deterministic and local to PA13.  The audit found no
reference-binary calls, copied runtime payloads, interpreter/VM/trampoline
substitutes, source-shape gates, timeout workarounds, or file-audit bypasses in
the PA13 implementation files.  `dev/frontend_source_sets.mk` wires the new
PA13 implementation files only into `FRONTEND_OBJ_BASENAMES_lowir2cy86`, so
earlier assignment tools are not linked against the PA13 adapter.
