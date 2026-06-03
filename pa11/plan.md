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
