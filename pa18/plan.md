# PA18 implementation plan

## Target

Extend the existing PA12 semantic parser and PA14 LowIR path with first-tier
template support. Instantiated templates must become ordinary record/function
bindings and semantic nodes so PA14 continues to lower the same PA17 shapes.

## Design

- Keep implementation in `dev/src` and reuse the current single-pass semantic
  model.
- Represent template declarations as owned PA12 compiler state, not text-only
  fixtures:
  - type parameter names, default type arguments, and declaration token ranges
  - owning scope for unqualified lookup at definition time
  - instantiated class/function specializations keyed by canonical argument
    types
- For class template-id use, parse type arguments, merge defaults, then replay
  the stored class declaration body in an instantiation context that maps
  template parameters to concrete `TypePtr`s. The result is an ordinary complete
  record type with normal class scope, members, constructors/destructors, layout,
  and generated special members.
- For function templates, store the function declaration/definition token range
  and instantiate on explicit template-id calls or direct-call deduction from
  ordinary argument types. Instantiated functions are ordinary function bindings
  and function-definition nodes.
- Keep lookup and overload participation integrated with existing
  `lookup_*`, `resolve_call_candidate`, ADL, hidden friend, member access, and
  LowIR demand paths.
- Reject unsupported PA18-out-of-scope forms by normal semantic failure rather
  than fallback code generation.

## Validation

- Use focused PA18 tests for diagnosis:
  `make test-report ACTIVE_TEST_REPORT_PAS='pa18'`.
- After semantic/lowering changes, run the required through check:
  `make test-report-through-pa18`.
- Run the file audit:
  `perl scripts/cppgm_file_audit.pl --stage pa18 --paths dev/src`.
- Commit cohesive progress only after stable checkpoints and leave the worktree
  clean when PA18 is complete.

## Architecture Review

- PA18 template state is owned by PA12, not by LowIR text or test fixtures.
  `pa12_templates.cpp` registers class templates, tracks template parameters and
  default arguments, keys class specializations by canonical argument types, and
  replays supported class bodies into ordinary record scopes.
- Function-template support lives in `pa12_templates_functions.cpp`; overload
  resolution sees placeholder function bindings, but selected explicit or
  deduced specializations become ordinary `Binding` and function-definition
  nodes before PA14 lowers them.
- Template-body validation now lives in `pa12_templates_validation.cpp`. It
  validates against a temporary owner scope and restores PA12 side tables after
  parsing, preserving only the dependent-base marker needed by later
  instantiations.
- `pa11::Type` carries an explicit `is_template_specialization` bit for class
  template instantiations. PA14 uses that metadata through helper functions
  rather than re-deriving semantic facts from record-name spelling.
- PA14 remains a demand-driven LowIR lowerer: inline instantiated functions are
  registered as normal semantic nodes, declarations and lifecycle helpers stay
  in `pa14_lowir_program_io.cpp`, and no template runtime, interpreter,
  trampoline, embedded payload, or reference-tool path is used.

## Final notes

- Template implementation is split across `pa12_templates.cpp` for declaration
  registration/class replay, `pa12_templates_functions.cpp` for function
  instantiation/deduction, and `pa12_templates_validation.cpp` for side-effect
  contained template-body validation.
- LowIR program emission keeps inline-demand logic in `pa14_lowir_program.cpp`
  and declaration/lifecycle/write helpers in `pa14_lowir_program_io.cpp`.
- Parameter declarations now use temporary function parameter scopes, preserving
  names for later parameter `decltype` use without leaking them into class or
  namespace lookup.

## Final Architecture Review

- The final implementation matches the PA18 boundary: supported templates are
  represented as semantic declarations and instantiate to ordinary PA11/PA12
  records, functions, members, constructors, destructors, and expression nodes
  before PA14 emission.
- Audit cleanup removed the two architecture risks found: validation-only class
  records no longer pollute real scopes or PA12 side tables, and PA14 no longer
  uses `<` in type names as a semantic test for template specialization context.
- File-audit pressure from the validation cleanup was resolved by placing the
  validation state helper in a registered `dev/src` translation unit instead of
  hiding code or weakening checks.
- No skipped compiler phases, dummy LowIR, template-binary/runtime substitutes,
  source-shape gates, timeout workarounds, or hidden unchecked implementation
  fragments remain in the PA18 audit surface.

- Final validation:
  - `make test-report-through-pa18`: 1360/1360 passed
  - `perl scripts/cppgm_file_audit.pl --stage pa18 --paths dev/src`: passed
