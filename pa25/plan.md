# PA25 Implementation Plan

## Contract

PA25 extends the existing PA24 source-to-LowIR compiler. Implementation belongs
in `dev/` and `dev/src/`; the `pa25/` directory remains the handout, harness,
and fixture surface.

The required language increment is:

- capturing lambdas, including explicit/default local captures and supported
  `this` capture
- `std::initializer_list<T>` interoperation for supported non-class element
  types
- deterministic RTTI and `typeid`
- pointer-form `dynamic_cast` over the existing single-inheritance polymorphic
  model

Reference-form `dynamic_cast` is lowered through `__cxa_bad_cast` for the
covered single-inheritance model. `dynamic_cast<void*>`, multiple inheritance,
virtual inheritance, init-captures, and class-element initializer lists remain
outside PA25.

## Design Boundaries

- Reuse the PA10 parse tree and the PA11/PA12 semantic model. New semantic facts
  should be carried in typed `Type`, `Binding`, `Node`, and parser/lowerer state,
  not recovered from formatted output.
- Extend the PA14-PA24 LowIR lowering path on demand. RTTI globals, closure
  helpers, initializer-list backing storage, and dynamic-cast runtime
  declarations should appear only when the source uses the corresponding PA25
  feature.
- Keep single-inheritance RTTI representation deterministic:
  type-info name global, RTTI object global, optional base RTTI pointer, and
  required external ABI vtable declarations.
- Lower pointer and reference `dynamic_cast` to ordinary LowIR control flow
  around the ABI `__dynamic_cast` runtime helper. Null pointer results stay
  null; null reference results call the ABI bad-cast helper.
- Treat `std::initializer_list<T>` as a recognized library type with builtin
  layout compatibility for `__begin` / `__size`, while preserving user-declared
  member functions used by overload resolution and calls.
- Closure classes should remain ordinary generated class types with fields for
  captures and an `operator()` body lowered through the existing method path.

## Implemented Shape

- `std::initializer_list<T>` is recognized semantically, supports braced-list
  conversion/deduction/`auto`, materializes a backing array in LowIR, and works
  with member calls and range-for over the builtin `__begin` / `__size` layout.
- Capturing lambdas are represented as ordinary generated closure records with
  capture fields, including explicit/default local captures and supported
  enclosing `this` capture through nested closures.
- RTTI/typeinfo emission is deterministic for polymorphic records, lambda
  records, pointer/fundamental typeinfo, and template-record cases whose ABI
  metadata can be emitted safely.
- Throw/catch lowering uses RTTI-compatible exception objects and host ABI
  runtime calls; throw lowering now lives in `pa14_lowir_throw.cpp` to keep
  exception ownership separate from general value-expression lowering.
- Call and object initialization lowering were split into focused helpers so
  the PA25 implementation stays inside the file-audit ownership limits.

## Completed Implementation Pass

This pass fixed an older-stage regression that blocked PA25 completion:
`pa3/tests/300-triple.t` timed out while evaluating many controlling
expressions. The fix keeps the real tokenizer/evaluator path, reduces phase
1/2 peak memory by combining trigraph replacement with line-splice deletion,
and streams `ctrlexpr` results per logical line instead of retaining the whole
test output in memory.

Completed validation:

```sh
make -C pa3 check TEST=tests/300-triple.t
make test-pa3
make test-report ACTIVE_TEST_REPORT_PAS='pa25'
make test-report-through-pa25
perl scripts/cppgm_file_audit.pl --stage pa25 --paths dev/src
```

The required through report passed `2345 / 2345`; the file audit passed with
warnings only.

## Validation

Use this loop while implementing:

```sh
make test-report ACTIVE_TEST_REPORT_PAS='pa25'
make test-report-through-pa25
perl scripts/cppgm_file_audit.pl --stage pa25 --paths dev/src
```

After each meaningful shared semantic/lowering fix, run the through check before
declaring progress stable, because older-stage regressions block PA25 completion.
