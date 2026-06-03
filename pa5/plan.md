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
  reusable stateful API and add dynamic predefined macro expansion for
  `__FILE__`, `__LINE__`, `__DATE__`, and `__TIME__`.
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
