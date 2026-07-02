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

## Validation Plan

1. Reproduce the clean `compare-pptoken-inception` include failure and identify
   the missing include as `<algorithm>`. Done.
2. Fix the PA39 generated host-config dependency for `preproc_support.o`. Done.
3. Validate the PA39 reproducibility checkpoints:

```sh
make -C pa39 compare-pptoken-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
make -C pa39 compare-cppgm++-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
```

Both PA39 compares pass with the dependency fix. Before returning, run the full
required exit set:

```sh
perl scripts/cppgm_file_audit.pl --stage pa39 --paths dev/src
make test-report-through-pa38
make -C pa39 test-through-pa10 CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
make -C pa39 compare-pptoken-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
make -C pa39 compare-cppgm++-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
```
