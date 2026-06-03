# PA10 Implementation Plan

## Scope

Implement `cppgm++ --emit-ast -o <outfile> <srcfile...>` as the next
compiler increment. The PA10 path will reuse the existing PA1-PA5 preprocessing
and posttoken pipeline, then parse each translation unit into explicit syntax
nodes and dump those nodes in the checked-in reference format.

This stage remains syntax-oriented. Parser state may record declared type,
template, namespace, and alias names so ambiguous forms can be parsed through
the PA10 grammar, but the AST dump will not perform type checking, lookup
validation, overload resolution, or semantic classification beyond that
syntactic disambiguation.

## Ownership

- `dev/cppgm++.cpp`: parse the PA10 command shape and delegate `--emit-ast`.
- `dev/src/pa10_ast.*`: own AST node storage, dumping, token collection, and
  the PA10 parser entry point.
- `dev/frontend_source_sets.mk`: link the new PA10 frontend module into
  `cppgm++` only.

No PA10 code will shell out to refs, host compilers, or test fixtures. The
parser consumes source tokens and produces the compiler artifact directly.

## Parser Design

- Convert preprocessed source into posttokens, retaining token spelling and
  token type names for deterministic leaves.
- Split `>>` logically only where template close-angle handling needs it while
  preserving `OP_RSHIFT:>>` expression output.
- Use a recursive-descent parser with:
  - declaration parsing for namespaces, linkage blocks, using forms, aliases,
    templates, classes/unions, enums, static assertions, function definitions,
    special members, and simple declarations;
  - declarator/type-id parsing that preserves pointers, references, arrays,
    parameter clauses, cv/ref qualifiers, exception specifications, default
    arguments, trailing returns, and member pointers;
  - statement parsing for compounds, conditionals, loops, labels, jumps, and
    try/catch;
  - precedence-based expression parsing for literals, id-expressions, calls,
    member access, unary/binary/conditional/assignment operators, casts, new,
    delete, type traits, lambdas, and braced initializer lists.
- Maintain scoped syntactic facts for names introduced by class/enum/typedef/
  alias/template declarations, namespace definitions, using declarations, and
  local typedefs so later declarations and type-ids are parsed from typed state
  rather than reinterpreting formatted AST text.

## Validation

1. Start with focused PA10 cases using
   `make test-report ACTIVE_TEST_REPORT_PAS='pa10'`.
2. After meaningful parser/dumper changes, run
   `make test-report-through-pa10` from the repository root.
3. Run `perl scripts/cppgm_file_audit.pl --stage pa10 --paths dev/src`.
4. Commit cohesive progress only when the implementation builds and the current
   checkpoint is stable.
