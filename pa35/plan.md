# PA35 Implementation Plan

## Scope

PA35 continues the existing `cppgm++ -c` hosted compile path. The target is to
compile the heavy standard-library headers through the current front end,
semantic model, lowering, and host-object emitter. Implementation changes belong
in `dev/` and `dev/src/`; `pa35/` remains the handout and harness area.

## Current Failure Shape

- PA35 stress is now concentrated in hosted template/SFINAE paths exercised by
  iostream, string, tuple, memory, and type-trait headers.
- The PA35 compiler behavior is currently test-clean through the full staged
  report, and the source-file audit over `dev/src` is a pass with warnings.
  Cleanup must continue to preserve the same parser, semantic, lowering, and
  object paths while avoiding new oversized files/functions, compressed
  implementation lines, or unchecked source islands.
- Rvalue stream forwarding overloads require alias templates with dependent
  default SFINAE arguments to preserve their alias identity until concrete call
  substitution can reject `enable_if<false>` candidates.
- Tuple constructors require a separate path for depth-0 instantiations that
  temporarily enter candidate depth only to complete dependent value-expression
  defaults. Those defaults should be preserved as dependent semantic state; true
  overload candidate substitution still rejects concrete disabled `enable_if`
  arguments.
- Through-gate regressions are PA35 blockers because PA35 builds on the same
  compiler pipeline. Recent audit refactors exposed older PA23/PA34 template
  substitution regressions; fixes must preserve those earlier stages before the
  PA35 gate can be considered stable.
- Recent ABI work for dependent `decltype` expressions must preserve typed
  expression semantics and Itanium substitution-slot ordering for qualified
  static calls, function types, casts, and template-id arguments. Follow-up
  fixes should continue in the ABI encoder and semantic template state, not in
  LowIR string post-processing.

## Design Direction

1. Diagnose PA35 failures from the smallest failing hosted header case upward,
   preserving the existing parser and typed semantic state.
2. Add parser concessions only for standard-library syntax that the current C++11
   compiler must accept in hosted headers. Keep those concessions in the normal
   declaration/type/template parsing path, not in test-name gates.
3. Fix semantic/template issues using existing typed structures such as
   `TypePtr`, `Binding`, `Scope`, `TemplateArgument`, and class/member
   instantiation records. Do not recover facts from dumped text.
4. Keep implicit special member generation synchronized with later declarations:
   once a user-declared constructor exists, stale implicit defaults must be
   removed from overload sets and generated LowIR queues instead of being hidden
   only by later overload filters.
5. Preserve explicit template-argument syntax on member function-template calls
   using parser state, then let the existing typed overload/template machinery
   reject overloads whose parameter kinds do not match.
6. Let dependent template-id primary names participate in function-template
   dependency probes, then reuse the existing class-template recovery and
   template-argument sequence matcher for template-template deduction.
7. Keep substitution failure handling scoped to template matching contexts:
   partial specialization matching may reject an invalid candidate, while the
   same invalid nested type remains a hard diagnostic in ordinary code.
8. Split pending-body replay into ordinary hosted bulk collection and forced
   replay for bodies demanded by object semantics. Do not manufacture vtable
   targets or emit declaration-only placeholders for inline virtuals.
9. Treat timeout cases as compiler algorithm problems. Prefer memoizing repeated
   type/template resolution, avoiding redundant class completion, or detecting
   re-entry with existing instantiation state over weakening compile work.
10. Leave object emission on the PA31/PA32/PA33/PA34 host-object path; PA35 only
   requires successful relocatable object creation, not link/runtime behavior.
11. Preserve dependent alias-template default arguments as typed
    `TemplateArgument`/`TypePtr` state. Do not flatten them into strings or
    decide overload viability from formatted type names.
12. Keep `enable_if<false>` rejection in actual candidate substitution contexts,
    but allow recovered depth-0 completion of dependent value-expression
    defaults to keep the already-selected declaration replayable.
13. Treat address-taken function template specializations as real object
    dependencies in the hosted compile path. Direct-call scanning alone is not
    enough for function-pointer initializers; forced LowIR body demand may replay
    a deferred hosted member-template body, while ordinary bulk hosted parsing
    remains deferred.
14. Seed forced body replay from actual translation-unit/object roots, not from
    every parsed hosted header function body. Hosted inline/template bodies are
    replayed when reached by that root-owned dependency closure; unrelated STL
    helper definitions stay deferred in compile-only PA35. Pre-existing inline
    extra bodies are scanned only after their binding enters that closure.
15. For hosted library helper templates whose bodies are intentionally deferred,
    preserve real typed call signatures at specialization time. Candidate
    caches must hold concrete `Function` types derived from semantic template
    arguments for small internal helpers such as `std::__write`; avoiding body
    replay must not return structurally-dependent or incomplete bindings to
    normal overload resolution.
16. Skip validation of non-root hosted library function-template definitions
    after their declarations have been parsed and recorded. PA35 depends on the
    declarations, substitutions, overload sets, and object-root closure, not on
    eagerly validating unreachable inline STL implementation bodies.
17. Model hosted member-template call candidates whose libstdc++ declarations
    expose dependent SFINAE return/default types after ordinary deduction:
    `std::function::operator=(_Functor&&)` and
    `std::vector::insert(const_iterator, InputIterator, InputIterator)` receive
    concrete typed function signatures from their owner record and call
    argument types, without attaching those candidates to deferred library
    bodies.
18. Treat common hosted wrapper conversions as typed semantic conversions, not
    textual matches: `__gnu_cxx::__normal_iterator<T*, C>` may convert to the
    corresponding const iterator, and `std::shared_ptr<T>` may convert to
    `std::shared_ptr<const T>` when the element qualification conversion is
    valid.
19. Normalize hosted `std::shared_ptr`/`std::__shared_ptr` specializations to
    their stable two-pointer object representation when libstdc++ internals
    leave a specialization incomplete during compile-only analysis. This keeps
    object sizing/layout available without replaying heavy unreachable hosted
    bodies.
20. In hosted mode, skip the extra early validation pass for hosted library
    function-template definitions and the small forwarding-template cases whose
    dependent bodies immediately expand large `std` candidate sets. Concrete
    non-library instantiations still parse and type-check their bodies, while
    declaration-time validation no longer copies the full template registry for
    unreachable standard-library implementation bodies.
21. Keep inherited/member operator-template lookup stable when recovered
    template-parameter-name heuristics inspect recursive class-template types.
    Cycle detection belongs in the typed `TypePtr`/template-argument traversal;
    lookup itself should still expose the inherited declaration and let normal
    overload selection instantiate the member operator template.
22. For function-template deduction against class-template specializations, use
    the pattern's stored template arguments when they carry dependent semantic
    state, but treat an actual instantiated record's completed
    `template_arguments` as authoritative. Stored actual match arguments may be
    stale after default-argument recovery; overload deduction should not reject
    `std::set<P, std::less<P>, std::allocator<P>>` because an auxiliary cache
    retained an older nested argument.
23. Keep constructor viability recursive-safe by rejecting copy/move-style
    constructors when the source argument is unrelated to the constructed
    record. Default constructor synthesis may still run after generated special
    members exist when no real zero-argument constructor is viable.
24. ABI substitution encoding needs re-entry protection for recursive
    dependent-typename context scopes. The encoder should track active
    `TypePtr` nodes in the substitution context and fall back to stable probe
    spelling on recursive re-entry, rather than walking class-scope template
    arguments until stack exhaustion.
25. Copy/move-style constructor pruning should remain a recursive-safety guard,
    but it must not preempt ordinary conversion-function analysis. When the
    source record exposes conversion operators, keep the candidate in the typed
    overload path and let `convert_to` decide whether a viable conversion to the
    constructor reference parameter exists.
26. Completed class-template instance arguments are authoritative for actual
    deduction records, including transitive base specializations. When a
    completed actual stores a parameter-pack slot as a `Pack`, match it directly
    against a deducible type-parameter-pack pattern instead of falling back to
    stale stored dependent base arguments.
27. Treat the file-audit cleanup as an ownership refactor, not a behavior
    change. Oversized files should donate whole methods or cohesive helper
    groups to responsibility-named `dev/src` modules that are added to
    `dev/frontend_source_sets.mk`; oversized methods should be split into typed
    helpers that operate on the existing compiler state rather than on formatted
    dumps or fixture-specific probes.

## Architecture Review

PA35 is implemented as an extension of the existing hosted compile pipeline, not
as a replacement path. The driver still preprocesses through `preproc_support`,
parses and type-checks through the PA12 model, lowers through the PA14 LowIR
builder, and emits host objects through the PA31+ object path. The PA35-specific
pressure valves are concentrated in typed compiler structures:

- Hosted function-template definition validation is skipped only for templates
  owned by `std`/`__gnu_cxx` or forwarding templates whose bodies mention `std`.
  Declarations, template parameters, overload sets, and specialization
  signatures are still recorded.
- Deferred hosted function bodies remain pending until demanded by expression
  semantics or LowIR object roots. `is_object_root`, explicit body-demand
  helpers, and address-taken function scanning keep object-relevant functions on
  the real replay/lowering path.
- Hosted STL modeling is narrow and typed: `std::function::operator=`,
  `std::vector::insert`, `std::__write`, `std::basic_string` operators,
  `__gnu_cxx::__normal_iterator` qualification conversion, and
  `std::shared_ptr` qualification/layout recovery operate on `TypePtr`,
  `TemplateArgument`, `Binding`, and namespace ownership, not on PA35 test names
  or dumped text.
- The audit refactor split large template/constexpr/member-body logic into
  responsibility-named modules and added them to `dev/frontend_source_sets.mk`.
  The split preserved ownership in `dev/src` and did not move implementation
  into handout directories or unchecked paths.

The performance story is based on deferring unreachable hosted implementation
bodies, reusing specialization/candidate signatures, and protecting recursive
template/type traversal. This is aligned with the PA35 contract: heavy headers
must compile within a workable budget, but PA36 owns hosted link/runtime
behavior.

## Final Architecture Review

The audit found no blocker requiring source changes. The implementation still
compiles real hosted headers through the normal compiler phases and writes a
real relocatable object; there is no reference-binary shell-out, templated
object payload, VM/interpreter substitute, or dummy object path in the PA35
compiler code. Searches for PA35 fixture names and reference-tool invocations in
`dev/` did not find source-shape gates.

File-audit warnings remain warnings, not failures: they identify older
catch-all/helper/header ownership and duplicate-helper debt plus a compressed
LowIR line that the audit script reports as a large literal risk. These are
visible in the required `cppgm_file_audit` output and are not bypasses; the PA35
files added by the audit refactor are built through the `cppgm++` source set.
No unresolved architecture, performance, regression, or cheating blocker was
found in this pass.

## Validation

- Use local `make -C pa35 check TEST=tests/compile/<case>.t` or
  `make test-report ACTIVE_TEST_REPORT_PAS='pa35'` for fast PA35 diagnosis.
- Use targeted earlier-stage checks when the through run reports a regression,
  then rerun `make test-report-through-pa35` after the fix.
- After meaningful parser, semantic, lowering, object, or shared infrastructure
  changes, run root `make test-report-through-pa35`.
- Run `perl scripts/cppgm_file_audit.pl --stage pa35 --paths dev/src` before
  completion.
- Commit cohesive progress only after the relevant build/test checkpoint is
  stable, and leave `git status --short` clean at handoff.
