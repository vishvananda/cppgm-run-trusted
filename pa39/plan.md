# PA39 Inception Plan

## Active Checkpoint

```sh
make -C pa39 compare-cppgm++-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
```

The saved Ralph log first reported a stale object mismatch at:

```text
obj/pa39/selfhost/shared/release/pa12_templates_typename_hosted.o
obj/pa39/inception/shared/release/pa12_templates_typename_hosted.o
```

Single-source probes and a clean PA39 rebuild showed that mismatch was not the
live bug: fresh host-seeded and self-built compiles both matched the larger
object containing the hosted `std::vector<TemplateArgument>` move-assignment
COMDAT output.

The clean rebuild exposed the real first blocker earlier, in
`compare-pptoken-inception`: `cppgm++-self` failed immediately with
`ERROR: include file not found` while compiling `pptoken.cpp`,
`pptoken_lib.cpp`, and `test_runner.cpp`.

## Owning Earlier Surface

This was a PA39 reproducibility/build dependency bug, not a new language feature
or a source-level compiler workaround. `dev/src/preproc_support.cpp` includes
`cppgm_builtin_host_config.h`, which records the host standard include paths
used for `-include-host`. PA39 generated that header, but the dependency was
attached to non-existent `../dev/src/preprocessor.cpp`, so a clean selfhost
`preproc_support.o` could be built with the fallback empty standard include path
table.

The resulting `cppgm++-self` searched only PA39 `-I` directories and the
repository fallback include paths. It failed to resolve the first standard
header, `<algorithm>`, during inception `pptoken` compilation. The fix is to
make the PA39 shared object for `../dev/src/preproc_support.cpp` depend on
`$(INCEPTION_BUILTIN_HOST_CONFIG)`, matching `dev/Makefile`.

No reducer is needed because the failure is in the PA39 checkpoint harness
dependency graph rather than a C++ semantic/compiler behavior.

## Architecture Review

PA39 is a staged rebuild harness around the already-owned compiler sources. It
does not add a new compiler language surface. Checkpoint membership comes from
`../dev/frontend_source_sets.mk`: `pa39/Makefile` includes that file, derives
`INCEPTION_SOURCES_*` from `FRONTEND_OBJ_BASENAMES_*`, and builds all shared
objects from those fixed lists. There is no generated source scan in the PA39
path.

The canonical self-host path builds `*-self` checkpoints under
`../obj/pa39/selfhost`, links them with `$(CPPGM_HOST_CXX)`, and uses the
stage-to-checkpoint mapping in `INCEPTION_CHECKPOINT_FOR_pa*` for preservation
tests. The earlier PA harnesses are invoked with `CPPGM_SKIP_DEV_REBUILD=1`,
empty `TEST_DEPS`, and the relevant staged binary (`CPPGM_TEST_APP`,
`LOWIROPT_APP`, or `LOWIR2NATIVE_APP`); this preserves the assignment
expectations while preventing each PA harness from rebuilding `dev/` over the
staged compiler being tested.

The canonical inception path builds `*-inception` through a recursive make with
`INCEPTION_COMPILER_FLAVOR=inception` and `CXX` set to
`$(INCEPTION_INCEPTION_CXX)`, normally `../obj/pa39/bin/selfhost/cppgm++-self`.
Each canonical `compare-*-inception` target depends on both the self and
inception binaries, then byte-compares them with `cmp`. During the inception
object build, `INCEPTION_COMPARE_OBJECTS` causes entry, shared, and runner
objects to be compared against the self-host objects as soon as they are
rebuilt. The diagnostic restored-self target is separate and explicitly disables
object compares only for that noncanonical path.

Reproducibility-sensitive generated input is limited to
`$(INCEPTION_BUILTIN_HOST_CONFIG)`, produced by `dev/gen_builtin_host_config.pl`
from `$(CPPGM_HOST_CXX)` and `$(CPPGM_STDLIB_FLAGS)`. PA39 now makes the
`../dev/src/preproc_support.cpp` shared object depend on that generated header,
matching `dev/Makefile`, so clean self-host builds cannot fall back to an empty
host include-path table. Missing-object scheduling is isolated from link order:
PA39 may build never-seen objects first, but final links still use
`inception_link_inputs` in canonical source-set order. Link outputs are written
through a `.tmp` file and replace the stable binary only on byte changes, which
avoids needless downstream rebuild drift when the linked bytes are unchanged.

The performance guardrails are part of the harness, not success shortcuts:
compile steps run through `scripts/run_with_timeout.pl`, the self-host timeout
and inception timeout are explicit variables, and the inception subbuild job
count is capped separately from the self-host object pass. The PA39 audit did
not find a timeout increase, fixture gate, dummy output, copied runtime,
embedded payload, interpreter, trampoline, or template-binary substitute in the
canonical build path.

## Validation Plan

1. Reproduce the clean `compare-pptoken-inception` include failure and identify
   the missing include as `<algorithm>`. Done.
2. Fix the PA39 generated host-config dependency for `preproc_support.o`. Done.
3. Validate the PA39 reproducibility checkpoints:

```sh
make -C pa39 compare-pptoken-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
make -C pa39 compare-cppgm++-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
```

## Final Architecture Review

The audited PA39 architecture remains a full-stage self-host and inception
compare around the real implementation source sets. The only PA39-specific
defect found in the current audit trail was the generated host-config dependency
on the wrong source path; the current Makefile fixes that by tying
`preproc_support.o` to `$(INCEPTION_BUILTIN_HOST_CONFIG)`.

Recent PA39-enabling source work stayed in `dev/` and `dev/src/`, and new
implementation `.cpp` files are listed in `dev/frontend_source_sets.mk`.
A mechanical source-set check found every listed source on disk and only
`dev/src/test_runner.cpp` outside the per-tool lists, which is intentional
because PA39 builds it through the dedicated runner rule. The earlier semantic,
lowering, backend, and optimizer fixes discovered while reaching inception have
reducers under their owning `cppgm.tests/course/paN` directories; the final
host-config dependency fix is a PA39 harness dependency issue and does not need
a language reducer.

The required final checks all passed in this audit run:

```sh
perl scripts/cppgm_file_audit.pl --stage pa39 --paths dev/src
make test-report-through-pa38
make -C pa39 test-through-pa10 CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
make -C pa39 compare-pptoken-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
make -C pa39 compare-cppgm++-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
```

`make test-report-through-pa38` passed 3461 of 3461 tests. The PA39
`compare-pptoken-inception` target reported `MATCH pptoken`, and the full PA39
`compare-cppgm++-inception` target reported `MATCH cppgm++`.
