# PA22 Implementation Plan

## Contract

PA22 extends the existing `cppgm++ --emit-lowir -O0` compiler path. The output
format remains PA13 LowIR; this stage owns the remaining C++11 template
deduction, substitution, overload participation, and no-eager-instantiation
behavior needed by the PA22 tests.

Implementation changes belong in `dev/` and `dev/src/`. The `pa22/` tree stays
as handout, harness, refs, and this plan.

## Starting Evidence

The root through report initially passed PA1 through PA21 and failed in PA22.
The failures clustered around:

- function-template deduction with explicit/defaulted arguments and template-id
  overload sets
- function-template partial ordering, including cv pointer/reference cases
- constructor/conversion function template participation and SFINAE candidate
  dropping
- delayed instantiation for dependent decltype, aliases, members, and layouts
- non-type template arguments for function/reference values

The PA22 file audit was already passing at the start, so implementation should
preserve the existing source split rather than adding broad monolithic code.

## Design Direction

- Keep semantic facts in typed structures: `TemplateDeclaration`,
  `TemplateArgument`, `TypePtr`, `Expr`, and `Binding`. Do not recover template
  identity, value category, or specialization facts from formatted names.
- Extend function-template deduction in `pa12_templates_functions.cpp` over the
  implemented type surface, including defaulted class-template arguments,
  pointer/reference/cv adjustments, arrays, function types, and explicit
  template-id candidates with too few or mismatched arguments.
- Treat substitution failure as overload-candidate state for template calls,
  constructors, conversions, and unevaluated `decltype` probes. Only emit a hard
  semantic error when no viable overload remains or the context is non-SFINAE.
- Add partial-ordering decisions where multiple viable function-template
  specializations remain, using typed parameter and argument comparisons rather
  than source declaration order or emitted names.
- Keep dependent bodies, member layouts, aliases, and calls lazy until the
  selected specialization is non-dependent. A dependent type mention should not
  complete a record or instantiate a function body unless ordinary semantic use
  requires it.
- Carry non-type template arguments as typed constant/function/reference
  bindings through parsing, substitution, instantiation keys, and LowIR naming.

## Implemented Shape

- Function template-id lookup preserves explicit arguments on the selected
  template placeholder or eager specialization, and overload resolution rejects
  unrelated existing specializations instead of treating them as candidates for
  the current template-id.
- Member template-id postfix handling attaches explicit arguments only to real
  function-template placeholders, so ordinary members and stale specializations
  are dropped naturally by the semantic candidate filter.
- Function-template instantiation keeps friend/member-body context and parses
  selected pending bodies only after a non-dependent overload has been chosen.
- LowIR constructor demand distinguishes base-entry calls from complete-entry
  calls while still emitting complete wrappers for user-provided constructors
  of class-template specializations that are demanded as base entries.

## Ownership Boundaries

- Parser and semantic changes should stay in the existing PA12 units:
  `pa12_templates_*.cpp`, `pa12_expr_*.cpp`, `pa12_decls*.cpp`,
  `pa12_types*.cpp`, and `pa12_internal.h`.
- PA11 type helpers may be extended only for genuine type identity or dependency
  support needed by deduction/substitution.
- LowIR changes should be limited to places where the semantic layer already
  produces the correct ordinary binding/type but lowering lacks the generic
  path.
- If a new `dev/src/*.cpp` file becomes necessary, add it to the appropriate
  list in `dev/frontend_source_sets.mk`.

## Validation Plan

1. Use `make test-report ACTIVE_TEST_REPORT_PAS='pa22'` and focused
   assignment checks while diagnosing pa22-only failures.
2. After meaningful parser, semantic, lowering, or shared infrastructure
   changes, run root `make test-report-through-pa22`.
3. Run `perl scripts/cppgm_file_audit.pl --stage pa22 --paths dev/src` after
   the through report passes.
4. Commit cohesive progress after stable checkpoints. Final handoff requires a
   clean `git status --short`.

## Final Evidence

- `make test-report-through-pa22` passes all PA1 through PA22 tests.
- `perl scripts/cppgm_file_audit.pl --stage pa22 --paths dev/src` passes.

## Architecture Review

The PA22 implementation extends the existing semantic pipeline rather than
adding a separate template interpreter. Function templates are represented by
`TemplateDeclaration` objects, placeholder `Binding`s, typed
`TemplateArgument`s, and substituted `TypePtr` function signatures. Call,
constructor, conversion, and address-taking paths instantiate candidates through
`instantiate_template_call_candidate()` and related helpers, and selected
specializations are lowered by the ordinary PA14 LowIR function/constructor
lowerers.

Deferred template body handling is owned by the PA12 parser state:
namespace-scope function template bodies are captured in
`pending_function_bodies_`, class/member bodies remain in
`pending_member_bodies_`, and ordinary semantic use calls
`parse_pending_function_body()` or `parse_pending_member_body()` before LowIR
needs the selected definition. The validation pass snapshots and restores the
same parser state, including pending bodies and template substitutions, so
definition probes do not leak generated declarations or partial parse state into
the real translation unit.

Non-type template arguments keep their typed value in `TemplateArgument`; when
the value is a function/reference binding, the binding remains attached as
`value_binding` for semantic identity and specialization matching. The PA11
template-instance argument used by record types now carries a stable
`value_name`, so LowIR type, RTTI, vtable, and ABI-support symbol construction
does not recover identity from raw pointer values.

LowIR emission remains declaration-driven. `pa14_lowir_emit.cpp` collects parser
output and demands inline definitions, object roots, hidden friends, generated
copy/move dependencies, globals, constructors, destructors, RTTI, and vtables
through `ProgramLowerer`. Generated empty constructors are still emitted only
for typed generated default/aggregate constructor bindings; arbitrary one-pointer
`void` functions are no longer converted into empty function bodies.

## Final Architecture Review

The audited architecture satisfies the PA22 handoff requirements:

- Template deduction, substitution, and SFINAE candidate dropping stay in PA12
  semantic code and use typed declarations, types, expressions, and template
  arguments.
- Deferred instantiation has a single parser-owned body queue model; LowIR does
  not parse source text, use reference binaries, or embed earlier IR payloads.
- Function-pointer and reference non-type template arguments have stable typed
  identity for both semantic caches and emitted LowIR naming.
- LowIR generation consumes selected semantic bindings and emits ordinary
  functions, constructors, globals, RTTI, and vtables without broad dummy-body
  fallbacks.
- The new `pa12_decls_declare_one.cpp` and `pa12_templates_variables.cpp` splits
  are listed in `dev/frontend_source_sets.mk`, and the audited source set passes
  the PA22 file audit.
