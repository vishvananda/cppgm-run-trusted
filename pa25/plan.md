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

## Architecture Review

The implemented PA25 architecture matches the staged PA24 compiler rather than
adding a replacement pipeline. Parsing and semantic ownership remain in the
`pa12_*` frontend files, with PA25 facts attached to typed `Type`, `Binding`,
`Expr`, and `Node` state. Lowering remains in the `pa14_lowir_*` family and
continues to emit ordinary LowIR text.

Feature ownership is split along existing boundaries:

- Capturing lambdas are built in `pa12_expr_primary.cpp` as generated closure
  records with capture fields and rewritten `operator()` bodies. LowIR object
  initialization then treats closure storage as normal record storage.
- `std::initializer_list<T>` recognition and conversion live in
  `pa12_expr_semantics.cpp`, declaration/range-for integration lives in the
  PA12 declaration and statement paths, and LowIR materialization lives in
  `pa14_lowir_object_init.cpp` / `pa14_lowir_init.cpp`.
- RTTI/typeinfo naming and deterministic global emission live in
  `pa14_lowir_rtti.cpp`; `typeid` lowering uses those globals through ordinary
  address/load/control-flow operations.
- `dynamic_cast` lowering is handled by `pa14_lowir_value_expr.cpp` and
  `pa14_lowir_value_addr.cpp`, using the ABI runtime declaration and ordinary
  LowIR branches for pointer null propagation and reference bad-cast handling.
- Source throw/catch lowering is isolated in `pa14_lowir_throw.cpp`, which is
  included in `dev/frontend_source_sets.mk`.

Audit review found one architecture issue: PA25 expression-kind checks for
`typeid` comparison and `dynamic_cast` dispatch were recovered from formatted
AST text/token strings. That has been replaced with typed `Node` flags so the
semantic and lowering paths no longer depend on presentation strings for those
PA25 facts.

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

## Final Architecture Review

The post-audit implementation has no discovered PA25 substitutes or bypasses:
no reference binaries, host compilers, interpreters, VMs, trampolines,
template-binary payloads, embedded earlier-IR payloads, fixture gates, or
timeout workarounds are used to produce compiler output.

The remaining string inspection in LowIR output ordering/pruning is presentation
reachability over already emitted LowIR symbols, not source semantic recovery.
The PA25 source semantic facts audited in this pass are represented explicitly:
initializer-list type recognition is typed, closure captures are represented as
generated fields, RTTI/typeinfo is emitted from `Type`/`Binding` structure, and
`typeid`/`dynamic_cast` expression identity is carried by `Node` metadata.

The PA25 file audit still reports warnings for legacy large/catch-all files and
known duplicate blocks, but it passes. The warnings were inspected as audit
signals; the PA25 cleanup did not move implementation into unchecked paths, and
the new throw lowering source remains in the frontend source set.

## Validation

Use this loop while implementing:

```sh
make test-report ACTIVE_TEST_REPORT_PAS='pa25'
make test-report-through-pa25
perl scripts/cppgm_file_audit.pl --stage pa25 --paths dev/src
```

After each meaningful shared semantic/lowering fix, run the through check before
declaring progress stable, because older-stage regressions block PA25 completion.
