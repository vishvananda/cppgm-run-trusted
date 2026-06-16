# PA36 Implementation Plan

## Scope

PA36 extends the existing hosted `cppgm++ -c` path from compile-only hosted
headers to host-linkable and runnable objects. Implementation remains in
`dev/` and `dev/src/`, reusing the current preprocessor, PA12 semantic model,
PA14 LowIR lowering, and PA31 host object writer.

## Current Failure Shape

- Current active PA36 stream smokes now reach host link, but chained hosted
  stream calls can execute the left operand more than once while PA14 computes
  hidden virtual-base ABI arguments for external `std::ostream` member calls.
  Lowering must preserve the already-materialized explicit object argument for
  externally owned hosted stream members instead of re-emitting side-effecting
  expressions such as `std::cout << "eof"`.
- `std::operator<<` free-function templates for hosted character and character
  pointer insertion are externally owned by libstdc++; the compiler should keep
  them semantic-only, reference the host ABI specialization symbol, and still
  materialize ordinary demanded inline bodies reached through function
  addresses such as stream manipulators.
- Several PA36 hosted container and functional smokes still expose missing
  concrete member-template bodies, wrong specialization ownership, or runtime
  lifetime bugs after the stream path is corrected. Those should be fixed from
  typed PA12 template bindings and PA14 demand emission rather than from raw
  symbol strings.
- Hosted container wrapper constructors can be declared in headers as
  in-class `= default` definitions, while their concrete member subobjects only
  become known after template completion. PA12 should synthesize the real
  defaulted constructor body from typed record fields/bases, and PA14 should let
  that synthesized non-empty body replace the earlier empty placeholder for the
  same binding.
- `std::initializer_list<T>` accessors are header-only semantic members backed
  by the list object's pointer/size fields. PA14 should lower `begin`, `end`,
  and `size` from the typed initializer-list record layout before the generic
  call path demands an external symbol.
- Hosted container bodies such as `std::_Rb_tree::_M_insert_unique` can be
  demanded through a concrete member-template binding while still carrying a
  stale dependent body expression from the primary template. Replay must apply
  both the concrete class-owner substitutions and the function-template
  arguments before PA14 sees the body, and dependent replay artifacts should not
  satisfy a concrete emitted-symbol demand.
- Earlier through-report failures are treated as regressions. The current dirty
  tree must return older stages to passing before handoff.
- PA27 now exposes a demand-ordering regression around template base
  constructors used by CRTP static downcasts: when the downcast source record
  is discovered while lowering an instantiated inline member, any constructor
  already demanded as a base entry must also be promoted to a complete entry
  through typed record ownership, not through emitted LowIR text.
- The current dirty tree also violates the PA36 file audit because earlier PA36
  growth pushed several implementation files and functions past ownership
  limits. Audit cleanup must move responsibility into named helper modules or
  smaller helpers without weakening behavior.

## Design Direction

1. Preserve GNU asm-label strings as typed declaration suffix state and store
   them on `Binding`; ABI symbol selection should prefer that explicit object
   name for both direct calls and definitions without changing overload
   resolution.
2. Keep hosted ABI names derived from semantic owners and real typedef/record
   facts. Replace placeholder local-type fallback only by threading the missing
   owner/name information through parsing, template instantiation, and the ABI
   mangler. Standard-library substitution abbreviations and numbered
   substitutions should be emitted by the central ABI helpers from semantic
   `TypePtr`/`Binding` state, including aliases between owner spellings already
   present in the nested-name prefix and later parameter type spellings.
3. Continue PA35's demand-driven hosted body model, but make the emitted-symbol
   closure link-complete for bodies reached from translation-unit roots.
   Unused hosted declarations should remain semantic-only; demanded inline and
   template bodies should emit weak/COMDAT definitions when owned by headers.
   The parser-side demand walk must include implicit lifecycle calls that
   lowering will synthesize from typed record state, especially destructors for
   temporaries, locals, fields, bases, and arrays. Those bindings should be
   added to the same object-root demand set as explicit calls so the body is
   materialized before LowIR registers inline definitions.
   Generic hosted inline bodies whose by-value ABI storage still contains
   template-parameter or dependent-typename storage should remain semantic-only;
   concrete instantiations must be demanded through their typed bindings.
   Ordinary out-of-class member definitions from class templates must bind to
   the matching concrete placeholder, not just to any overload with the same
   arity. In particular, copy and move `operator=` definitions differ by the
   reference category of the explicit object source parameter; PA12 should use
   parser token structure for the definition header plus the typed placeholder
   function type to queue the correct body for later LowIR demand.
4. Treat externally owned hosted stream members as calls that use the host
   library ABI surface exactly as the host object expects. PA14 should not
   synthesize extra hidden virtual-base arguments for these calls, because the
   explicit object argument already names a host `std::ostream` object/reference
   and recomputing it can repeat observable insertion side effects.
5. Classify hosted library value ABI from typed record facts. Small host types
   such as `std::fpos`/`std::streampos` must follow libstdc++'s direct register
   return/pass convention even when their parsed declarations expose user
   special members in headers; this belongs in the shared PA14 record ABI
   classifier, not in individual call lowering.
6. Keep object initialization and runtime helper ownership local to the object
   writer. Any compiler runtime entry that may appear in more than one object
   must be local, weak, or otherwise section-owned so ordinary host linking of
   multiple TUs is valid.
7. Fix relocation decisions in PA31 from the LowIR operation and symbol kind:
   imported function calls use PLT/call relocations, imported data loads use GOT
   when position-independent access is required, and internal data addresses use
   the existing PC-relative data relocation.
8. Implement hosted builtins and EH behavior through typed expression/lowering
   nodes and host runtime calls. Do not add harness-specific gates, reference
   shell-outs, copied executable payloads, or dummy object output.

## Ownership Boundaries

- Parser declaration suffixes and semantic facts belong in PA12 structures such
  as `DeclSuffix`, `Binding`, `TypePtr`, template declarations, and scopes.
- ABI spelling belongs in the existing PA12/PA14 ABI helpers that already
  consume semantic types and bindings.
- Demand-driven body replay and emitted-function ordering belong in
  `pa14_lowir_*`.
- ELF symbol binding, COMDAT/weak sections, relocations, GOT/PLT handling, and
  host EH tables belong in `pa31_host_object_*`.
- New regression tests, if needed, go under `cppgm.tests/course/pa36/`; PA36
  handout references are not edited.

## Architecture Review

- PA36 implementation remains in `dev/` and `dev/src/`; the PA36 handout
  tests and references are unchanged. New source ownership added during audit
  is registered in `dev/frontend_source_sets.mk`.
- Hosted body ownership is demand-driven. PA12 records template placeholders,
  specialization arguments, pending member bodies, and external ownership facts;
  PA14 demands concrete inline/header bodies from typed `Binding` and `TypePtr`
  state; PA31 emits host ELF symbols, relocations, weak/COMDAT sections, and EH
  metadata.
- The audit found one PA12 ownership violation: hosted stream insertion
  deferral wrote a raw Itanium specialization symbol in `pa12_statements.cpp`.
  That bypassed the central PA12 ABI mangler. The code now lives in
  `pa12_statements_hosted.cpp` and uses the existing
  `abi_function_template_specialization_symbol` path with the recorded
  `TemplateDeclaration` and concrete `TemplateArgument` vector.
- The CY86 `append_external_rtti_vtable_stubs_cy86` path was reviewed as an
  older standalone-runtime compatibility path, not the PA36 host-object path.
  PA36 object output keeps hosted/runtime references as ELF declarations and
  relocations through PA31.
- File audit warnings remain non-fatal and are tracked as broad historical
  ownership/formatting warnings. The PA36-blocking warning from the raw hosted
  stream symbol was removed, and the new hosted statement helper split keeps
  `pa12_statements.cpp` under the stage file-size limit.

## Final Architecture Review

- No dummy object generation, reference-binary shell-outs, copied executable
  payloads, fixture gates, timeout workarounds, or test-name gates were found
  in the PA36 implementation footprint.
- The externally owned hosted stream insertion path now preserves the same
  demand policy while deriving ABI spelling from semantic template facts instead
  of reconstructing it from a hand-coded string.
- The demand closure, hosted layout, LowIR lowering, and host-object writer
  still use typed compiler state for required definitions and symbol ownership.
  Remaining broad scans are over per-translation-unit emitted bodies or object
  records and did not present a PA36 performance blocker in audit.
- Final validation for this audit is the root through-report plus the PA36 file
  audit. Both are recorded in `pa36/audit.md`.

## Validation

- Use `make -C pa36 check TEST=tests/link/<case>.t` and
  `make test-report ACTIVE_TEST_REPORT_PAS='pa36'` for fast diagnosis.
- After meaningful parser, semantic, lowering, object, runtime, or shared
  infrastructure changes, run `make test-report-through-pa36`.
- If through-report failures appear before PA36, treat them as regressions and
  fix them before continuing PA36 work.
- Before handoff, run:
  - `make test-report-through-pa36`
  - `perl scripts/cppgm_file_audit.pl --stage pa36 --paths dev/src`
- Commit cohesive progress and leave `git status --short` empty.
