# PA5 Implementation Plan

## Contract

`preproc` is the next stage of the same compiler pipeline. It reads one or
more source files, executes phases 1 through 6 plus phase-7 tokenization, and
writes PA2 post-token descriptions inside `preproc`/`sof`/`eof` sections.
Earlier PA1-PA4 behavior must remain the shared implementation, not a separate
PA5-only path.

## Ownership

- `pptoken_lib` remains the owner of source decoding, trigraphs, line splicing,
  comment handling, header-name tokenization, and preprocessing-token spelling.
  PA5 will extend its stream callback with source locations so `__LINE__`,
  `__FILE__`, `#line`, macro replacement, and include diagnostics use typed
  token state.
- `macro_support` remains the owner of macro definitions, redefinition checks,
  argument collection, stringizing, token paste, placemarkers, variadics, and
  unavailable-name painting. PA5 will expose the existing processor as a
  reusable stateful API, add dynamic predefined macro expansion for
  `__FILE__` and `__LINE__`, and add fixed build-stamp predefined macros for
  `__DATE__` and `__TIME__`.
- `ctrlexpr_support` remains the owner of typed controlling-expression
  conversion and evaluation. PA5 will call it with a real macro-defined
  predicate instead of the PA3 mock.
- `preproc_support` will own PA5-specific orchestration: logical-line
  directive parsing, conditional-inclusion stack state, include recursion,
  `#pragma once` file-id tracking, `_Pragma` execution after macro replacement,
  `#line` file/line state, and output token collection.
- `dev/preproc.cpp` stays a thin command-line entry point and file writer.

## Directive Design

Each source file gets independent PA5 state: macro table, predefined macro
values, conditional stack, and `#pragma once` set. Include files share that
state with the including source while top-level command-line source files do
not share state with each other.

Processing is line based over located preprocessing tokens. At each logical
line, PA5 distinguishes directives only when the first real token is `#` or
`%:`. Active text lines are macro-expanded, `_Pragma` operators are executed
and removed, and the resulting preprocessing tokens are appended for PA2
post-tokenization. Inactive text is skipped, while nested conditional directive
ordering is still validated.

Conditional directives push/update/pop explicit states tracking parent
activity, whether a branch has already been taken, and whether `#else` has
already appeared. `#if`/`#elif` use PA4 control-expression macro expansion and
PA3 typed evaluation; `#ifdef`/`#ifndef` query the macro table directly.

`#include` macro-replaces its operand in active sections, resolves either a
header-name or ordinary string-literal operand, searches first relative to the
current presumed `__FILE__` directory and then relative to the process working
directory, skips files whose file id was marked by `#pragma once`, and otherwise
recursively processes the included file without emitting `sof`/`eof`.

## Architecture Review

The implementation matches the planned ownership split. `dev/preproc.cpp`
collects arguments, computes the single `asctime` build stamp, opens the output,
and delegates all compiler behavior to `preproc::run_preproc`. PA5-specific
orchestration lives in `dev/src/preproc_support.cpp`: it tokenizes each physical
file through `pptoken::run_pptoken`, applies presumed file/line state to tokens,
groups logical lines, maintains the conditional stack, dispatches directives,
recurses through includes, records `#pragma once` file ids, executes `_Pragma`,
and passes the resulting token stream to PA2 post-token emission.

The reused libraries remain shared rather than forked. `pptoken_lib` performs
phase 1 through 3 source translation, appends the final newline, recognizes
header names, and reports token source locations through `IPPTokenStream`.
`pp_token` stores token kind, spelling, macro-unavailability paint, active paste
state, and source location. `macro_support` owns macro definitions, macro
replacement, argument caching, stringizing, token paste, dynamic predefined
macro hooks for `__FILE__` and `__LINE__`, and fixed predefined macros for the
PA5 build facts. `ctrlexpr_support` owns PA3 typed expression evaluation and is
called from PA5 with the real macro-defined predicate. `posttoken_pipeline`
continues to own conversion from preprocessing tokens to PA2 output and reports
invalid token emission back to PA5 for the required failure path.

The audit did not find a skipped phase, fallback success path, dummy output,
test-specific gate, host-toolchain dependency, embedded payload, or reference
binary dependency. Performance-sensitive state is represented directly on
tokens or in PA5 state (`IfFrame`, `once_files_`, source file/line fields,
macro definitions, and cached macro arguments); no downstream recovery from
fixture text or repeated full-suite walks is used.

## Validation

Fast diagnosis uses:

```sh
make test-report ACTIVE_TEST_REPORT_PAS='pa5'
```

After parser, semantic, macro, include, or output changes, the required gate is:

```sh
make test-report-through-pa5
perl scripts/cppgm_file_audit.pl --stage pa5 --paths dev/src
```

Stable checkpoints should be committed cohesively, and the final handoff
requires a clean `git status --short`.

## Final Architecture Review

After the audit cleanup, the architecture remains the staged compiler pipeline
described above. The only implementation cleanup was local to
`preproc_support`: file-id scratch storage is initialized before the Linux
`stat` syscall fills it, directive and `_Pragma` token copies reserve their
known capacity, and the unused retained `Options` copy was removed from
`Preprocessor`. These changes reduce audit noise and hot-path allocation churn
without changing directive semantics or moving behavior across ownership
boundaries.

The final shape is suitable for moving beyond PA5: `preproc` emits real PA2
token descriptions from the shared tokenizer, macro processor, controlling
expression evaluator, and post-token pipeline; includes and top-level source
files have the required state isolation; and source files added for PA5 are
registered in `dev/frontend_source_sets.mk` for the `preproc` tool.
