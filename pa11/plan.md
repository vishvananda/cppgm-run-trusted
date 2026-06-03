## PA11 implementation plan

### Compiler design

PA11 will add a real `--emit-types` path to the existing `cppgm++` driver. The
new path will continue to use the existing preprocessing/post-token pipeline
and will run the PA10 parser as the syntax boundary before semantic analysis.

The semantic implementation belongs under `dev/src` as a PA11 module:

- public entry point: `pa11::emit_types(srcfiles, outfile, options)`
- model/state: canonical PA11 `Type`, `Binding`, `Scope`, and
  `TranslationUnit` objects
- parser/analyzer: a token-driven declaration analyzer that builds scope trees,
  performs lookup, derives declarator types, and evaluates the PA11 constant
  subset
- emitter: deterministic dump writer matching the checked-in `.ref` files

The driver change is limited to wiring `--emit-types` to this module. PA10
`--emit-ast` remains unchanged.

### Ownership boundaries

The PA11 model owns all semantic facts needed for the dump: scopes, namespace
aliases, using directives, bindings, canonical types, enum values, and constant
integer values for supported `const`/`constexpr` objects. Later phases should be
able to reuse these facts without recovering semantics from formatted output.

Namespaces are reopened by reusing the existing namespace scope. Class, enum,
function, block, and template-parameter scopes are child scopes in declaration
order. Bindings are stored in declaration order and emitted before child scopes,
matching the PA11 reference format.

### Feature increments

1. Driver, source-set, and dump scaffolding for successful empty translation
   units.
2. Namespace scopes, aliases, using directives/declarations, typedefs,
   alias-declarations, simple variables, functions, and declarator-derived
   pointer/reference/array/function types.
3. Class scopes, forward declarations, nested classes, class member variables
   and functions, function parameter scopes, and block-scope declarations.
4. Enum types, scoped enum scopes, unscoped enumerator injection, opaque scoped
   enums, supported underlying-type checks, and enumerator constants.
5. PA11 constant-expression subset for array bounds, `sizeof(type-id)`,
   `alignof(type-id)`, `decltype`, `static_assert`, and supported qualified
   lookup through namespaces, classes, enum scopes, aliases, and using
   directives.
6. Template-parameter scopes for type and template-template parameters.

### Validation

Use the fast PA11 report while iterating:

```sh
make test-report ACTIVE_TEST_REPORT_PAS='pa11'
```

After meaningful parser, semantic, or shared infrastructure changes, run:

```sh
make test-report-through-pa11
perl scripts/cppgm_file_audit.pl --stage pa11 --paths dev/src
```

Older-stage regressions in the through report are blockers and must be fixed
before treating PA11 as complete.

### Architecture Review

The implemented PA11 path follows the planned architecture.  `dev/cppgm++.cpp`
dispatches `--emit-types` to `pa11::emit_types`, while `--emit-ast` remains on
the PA10 path.  `pa11::analyze_source_file` uses the shared preprocessing and
post-token pipeline, runs the PA10 parser as the syntax boundary, and then
builds PA11 scopes and bindings from the token stream.

The semantic model in `dev/src/pa11_internal.h` and
`dev/src/pa11_model.cpp` owns the PA11 facts used by the dump: `Type`,
`Binding`, `Scope`, namespace aliases, using directives, child-scope order,
binding order, enum constants, and supported object constants.  Emission in
`dev/src/pa11_emit.cpp` walks those model objects directly and does not recover
semantic facts from formatted strings or fixture output.

The parser/analyzer in `dev/src/pa11_parser.cpp` is token-driven and remains
bounded by the PA11 assignment slice.  Stateless declaration-specifier helpers
live in `dev/src/pa11_support.cpp`, which keeps the parser under the file-audit
line limit and is registered in `dev/frontend_source_sets.mk` for the
`cppgm++` tool.

The audit found no reference-binary calls, host compiler shell-outs,
interpreter/VM/trampoline paths, embedded output payloads, fixture-name gates,
or skipped PA10 syntax phase in the PA11 implementation.  Lookup is map-based
inside each scope and recursively follows using directives with a visited set,
so using-directive cycles do not produce unbounded recursion.

### Final Architecture Review

After cleanup, PA11 preserves the intended ownership boundaries and deterministic
dump surface.  Block-scope recovery now falls back to statement skipping only
before the parser has committed to a declaration; declaration-shaped semantic
failures propagate as PA11 failures.  Anonymous class, struct, union, and enum
types now have deterministic semantic identities instead of empty or
misleading names.  Template-template parameter lists parse in an isolated
parameter scope so inner names do not leak into the enclosing template body.
Enumerator initializers must evaluate successfully before their value is
stored.

The final source layout keeps PA11 implementation under `dev/src`, with the new
`pa11_support.cpp` included in the `cppgm++` source set.  Earlier-stage timeout
regressions found by the required through report were fixed in the relevant
hot paths: PA3 now avoids per-line iostream output overhead in `ctrlexpr`, and
PA9 emits RIP-relative x86-64 memory accesses for label-addressed CY86 memory
operands.  Those changes are general performance fixes, not timeout-budget or
fixture-specific gates.
