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
- `dev/src/pa10_ast.h`: expose the PA10 `emit_ast` entry point.
- `dev/src/pa10_internal.h`: own shared AST node, token, scope, and parse
  result declarations.
- `dev/src/pa10_parser_internal.h`: declare the private recursive-descent
  parser interface.
- `dev/src/pa10_support.cpp`: own AST storage/dumping, preprocessing and
  posttoken collection, `>>` token splitting, and the `emit_ast` entry point.
- `dev/src/pa10_parser.cpp`, `dev/src/pa10_decls.cpp`,
  `dev/src/pa10_types.cpp`, and `dev/src/pa10_expr.cpp`: own parser state,
  declaration parsing, declarator/type-id parsing, statement parsing, and
  expression parsing.
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

## Architecture Review

The implemented PA10 path follows the staged frontend boundary.  `dev/cppgm++.cpp`
handles the long-lived `cppgm++` command surface, rejects unsupported emit-mode
options for PA10, builds preprocessor options, and delegates `--emit-ast` to
`pa10::emit_ast`.  The PA10 implementation is linked only into `cppgm++`
through `dev/frontend_source_sets.mk`.

`pa10_support.cpp` runs each source file through the existing PA1-PA5
preprocessing and checked posttoken pipeline, splits `>>` into paired logical
`>` tokens for template close-angle parsing, preserves split-group metadata so
right-shift expressions still dump as `OP_RSHIFT:>>`, and emits translation
units in command-line order.

The parser is a recursive-descent syntax parser split by surface area:
`pa10_parser.cpp` owns token movement, scopes, namespace/class fact tables,
template-angle text handling, and common probes; `pa10_decls.cpp` owns namespace,
using, alias, template, class, enum, static-assert, linkage, and explicit
instantiation declarations; `pa10_types.cpp` owns decl-specifier, declarator,
type-id, parameter, suffix, and initializer syntax; `pa10_expr.cpp` owns
statements and expressions.

AST nodes retain the required deterministic line dump, but parser decisions use
explicit metadata for builtin function-style names, qualified type-ids, leading
type names, declaration-specifier state, namespace imports, class member type
facts, inherited type names, and one-shot qualified member function body imports.
The parser no longer depends on reparsing formatted AST lines to decide whether
later syntax is a type-id, expression, trailing return annotation, or builtin
function-style cast.

The implementation produces the PA10 AST directly from source tokens.  It does
not shell out to reference binaries, host compilers, interpreters, VMs, or
helper scripts; does not embed earlier compiler payloads; and does not branch on
test filenames or fixture contents.  Parser scans are bounded to local lookahead
or balanced token ranges for the current declaration/expression, with no
full-suite or repeated translation-unit walks in hot paths.

## Final Architecture Review

The audit cleanup kept the PA10 parser architecture and fixed the ownership
problems found inside it.  Type names are no longer inserted into every active
scope.  Template parameter names stay in template-parameter scopes, namespace
members are recorded in namespace tables and imported through using directives,
inline namespaces, aliases, and reopened namespace scopes, and class member
types are recorded under their owning class and imported into derived classes or
qualified member function bodies only where that syntax context needs them.

Stringly parser facts were replaced with structured fields on parse results and
AST nodes.  Declaration-specifier continuation, non-type template defaults,
builtin function-style casts, qualified type-id disambiguation, trailing return
type labeling, namespace-qualified template names, inherited typedef casts, and
qualified return-type casts now use parser metadata rather than formatted dump
line inspection.

The private parser declaration was split into `pa10_parser_internal.h` so PA10
does not leave a file-audit header-body warning.  The remaining file-audit
warnings are pre-existing PA7/PA8 `nsdecl`/`nsinit` ownership and duplication
warnings outside the PA10 implementation.

No skipped compiler phase, dummy output path, runtime/interpreter/trampoline
substitute, template-binary or embedded-payload substitute, test-specific gate,
timeout workaround, file-audit bypass, duplicated PA10 semantic ownership, or
PA10 performance blocker remains from the reviewed implementation.
