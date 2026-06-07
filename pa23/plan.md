# PA23 Implementation Plan

## Scope

PA23 is the integration pass for the template machinery added through PA18,
PA19, PA21, and PA22. Implementation work stays in `dev/` and `dev/src/`, and
continues to lower through the existing PA14-PA22 LowIR path. The `pa23/`
directory remains a handout and test surface except for this plan.

## Compiler Design Focus

- Preserve typed `TemplateArgument` state for type, value, template, and pack
  arguments across alias expansion, substitution, deduction, partial
  specialization selection, static data/member lookup, and LowIR symbol
  generation. Do not recover semantic facts from formatted names.
- Carry dependent qualified value metadata, including source owner/member names
  and logical negation, through default template arguments, template instance
  arguments, expression replay, and constant-expression comparison so enable-if
  and bool non-type arguments can be resolved after substitution.
- Evaluate substituted non-type template expressions as real constant
  expressions when their operands become concrete, including bool results from
  comparisons and integral member constants referenced through dependent
  owners.
- Replay dependent qualified and member lookups in the instantiated scope with
  the original owner, current-specialization context, and template argument
  bindings intact.
- Replay deferred member bodies with the concrete owning class specialization's
  type, value, and pack substitutions layered over the original declaration
  context.
- Treat substitution failures inside immediate template contexts as candidate
  removal, while keeping hard diagnostics for non-SFINAE contexts and invalid
  explicit specializations.
- Prevent recursive integration cases from re-entering the same incomplete
  class/function/template instantiation. Use existing instantiation state and
  add narrow typed guards where needed; do not suppress work or weaken the
  harness.
- Demand-complete class-template specializations that are semantically needed,
  while allowing speculative function-template candidates to remain candidate
  only until selected.
- For constructor-template overload resolution, instantiate speculative
  candidates only far enough to substitute/check their function type and
  template defaults. Once overload resolution selects a constructor template in
  an evaluated context, immediately replay the selected specialization body so
  inherited and forwarding constructor LowIR still lowers through normal inline
  function emission.
- Keep lowering unaware of template subsets: instantiated declarations should
  be ordinary typed declarations by the time LowIR emission sees them.
- Preserve ABI symbol stability for dependent explicit function-template calls
  by reserving only the primary symbol names that were actually referenced
  through template-id syntax.
- For constructor-template integration, preserve semantic overload resolution
  in PA12 and let PA14 reuse already-instantiated same-template-family
  constructors when lowering same-record object copies. Generated copy/move
  constructors that are selected by typed state must have real LowIR bodies,
  and function-template constructor specializations must not alter trivial
  record pass/return ABI.
- When two constructor-template candidates instantiate to the same concrete
  function type, keep their template-origin metadata in overload resolution and
  apply the normal function-template partial-ordering tie-break before treating
  them as duplicates.
- Bind out-of-class member-template definitions, including nested template
  declarations, to the concrete owner placeholder when a class specialization
  is completed.
- Preserve default template arguments when an out-of-class function, conversion,
  or constructor template definition is matched to an earlier placeholder. The
  selected body declaration should own the defaults for later deduction and
  SFINAE completion.
- For function template-ids that are first parsed with dependent pack
  arguments, keep the placeholder/template-declaration relationship available
  during later pack expansion so each concrete element can instantiate through
  ordinary overload resolution rather than reusing the earlier dependent
  specialization binding.
- Match class partial specializations with pack-expanded stored arguments using
  typed pack contents from `record_template_arguments_`, so empty and non-empty
  packs participate in ordinary partial ordering.
- Treat the course-provided internal type transforms used by PA23 fixtures
  (`__decay`, `__remove_reference_t`, `__remove_cv`, and `__remove_cvref`) as
  typed alias-transform operations during type parsing. They should return
  normal `TypePtr` results so alias templates, deduction, and lowering see
  ordinary substituted types.
- Keep template-declaration body skipping syntactic only, but balanced enough
  for PA23 alias and variable templates: braced non-type template arguments
  inside a skipped declaration are not declaration bodies and must not expose
  the following comma or closing angle token to namespace parsing.
- Preserve template-id arguments on dependent member typename components such
  as `typename Alloc::template rebind<U>::other`. Resolution after
  substitution must instantiate the member alias/class template through the
  concrete owner scope instead of treating the formatted `rebind<>` spelling as
  an ordinary type member name.
- Rebind member class templates declared inside selected class-template partial
  specialization bodies by the typed outer template family when the concrete
  specialization is represented by a rebound declaration object.
- When a dependent qualified non-type member such as `Owner<Args...>::value`
  is stored in a `TemplateInstanceArgument` through an earlier type-like parse,
  recover it as a typed dependent value member during substitution rather than
  dropping the owner arguments or re-parsing the formatted spelling.
- Keep deferred `decltype(...)` operands replayable from typed dependent
  typename state. Replay happens under the current substitution stack so ADL,
  SFINAE, and value-category rules are evaluated when the operand becomes
  concrete.
- Specialize function-template declarations without definitions from their
  stored generic function type instead of reparsing declaration tokens. This
  keeps unevaluated helpers such as `declval<T>()` usable during replay and
  avoids coupling template semantics to the active token buffer.
- Preserve hard diagnostics from template-argument completion while registering
  function template declarations. Alternate-form probes may recover constructors
  and member templates, but a parsed declaration with a known template-id must
  not be silently downgraded to an empty variable template after a kind or arity
  mismatch.
- Encode dependent non-type template arguments for symbols from preserved
  expression spans and typed dependent type state. Return types such as
  `typename meta::enable_if<sizeof(T) < sizeof(long), int>::type` must produce
  stable ABI names without rebuilding semantics from formatted diagnostics.
- Treat compiler-intrinsic-shaped type trait expressions that appear in reduced
  library SFINAE code as typed bool expressions only when there is no ordinary
  user declaration to call. Dependent operands must keep their expression span
  for later substitution; concrete operands should ask the existing
  initialization and overload-resolution machinery instead of becoming a
  text-only shortcut.
- When a member-template candidate from a class-template partial specialization
  has an implicit object parameter described by the substituted partial pattern,
  overload resolution should treat a concrete same-primary class specialization
  object as the same owner for that object argument only. Do not rewrite the
  stored declaration type or constructor-template body ownership to get there.
- In unevaluated function calls used by library traits and size probes, run
  ordinary overload resolution and preserve the selected function type, but do
  not queue substituted parameter class specializations for end-of-translation
  unit completion merely because the selected overload mentions them.
- Replayed dependent `decltype` operands may still be dependent when a class
  partial-specialization owner is concrete but the member template's own
  parameters are not. Keep the original operand replayable until all relevant
  substitutions are concrete.
- When a typedef names a dependent `decltype(...)`, qualified lookup through
  that typedef should ask the typed substitution/replay path directly before
  resolving the qualifier scope, so concrete class specializations can expose
  members such as `type::value`.
- The same replay-before-scope rule applies to direct
  `decltype(expr)::member` qualifiers in SFINAE probes.
- Function-template candidate instantiation should use the stored generic
  function type and the dependent-return replay machinery, not declaration-span
  reparsing, so candidate selection does not depend on the currently active
  token buffer or instantiate helper bodies from unevaluated probes.

## Ownership Boundaries

- Parser and semantic fixes belong in `dev/src/pa12_*` files, primarily the
  template, expression, declaration, lookup, record, and static-assert units.
- LowIR fixes belong only in `dev/src/pa14_*` when typed template facts are
  already present but emitted symbols or globals are wrong.
- New source files are ownership-preserving splits of existing PA12/PA14
  modules only. Each split module must stay responsibility-named and be added
  to `dev/frontend_source_sets.mk` for `cppgm++`.
- Tests may be added under `cppgm.tests/course/pa23/` only for focused
  regressions that are not already covered by PA23 handout tests.

## Validation Plan

1. Use single-test PA23 checks to inspect the first failure and any timeout
   reproducer after each targeted fix.
2. Run `make test-report ACTIVE_TEST_REPORT_PAS='pa23'` for scoped PA23
   feedback while diagnosing integration clusters.
3. After meaningful semantic, lowering, or shared infrastructure changes, run
   `make test-report-through-pa23`.
4. Run `perl scripts/cppgm_file_audit.pl --stage pa23 --paths dev/src`.
5. Commit cohesive progress only after a stable checkpoint, and finish with a
   clean `git status --short`.
