## CPPGM Programming Assignment 39 (Inception)

### Overview

PA39 is the inception assignment. To complete it, make `cppgm++` rebuild
itself and match the host-seeded build byte for byte:

```sh
make compare-cppgm++-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
```

PA39 does not add a new language feature, command-line mode, object format,
runtime ABI, optimizer pass, or backend surface. It checks whether the compiler
implemented through PA38 can compile its own source reproducibly.

### The Build Layers

Keep the compiler layers separate while debugging:

- `../dev/cppgm++` is the host-seeded course compiler. It is built from the
  current source with the host toolchain.
- `*-self` checkpoint binaries are built from the same source by
  `../dev/cppgm++`.
- `*-inception` checkpoint binaries are built from the same source by the
  corresponding `*-self` compiler.

When a self-built compiler behaves differently from `../dev/cppgm++`, assume
the self-built compiler may have been miscompiled. Do not patch the failing
runtime path first. Trace the divergence back to the source file, object, or
compiler feature that produced the bad self-built compiler.

### Debugging Failures

Treat every PA39 failure as an earlier compiler bug until proven otherwise.
The first question is which layer first diverges.

If `../dev/cppgm++` fails to compile a reduced source, debug it like any
earlier assignment failure:

1. Reduce the source to the smallest construct that still fails.
2. Identify the earliest PA that owns the parser, semantic, lowering,
   optimizer, backend, runtime, or reproducibility behavior.
3. Add the reducer under the matching `cppgm.tests/course/paN` directory.
4. Fix that earlier compiler surface and rerun the narrow test.

If `../dev/cppgm++` compiles the source but a `*-self` compiler fails, debug
the self compiler as a possibly miscompiled program:

1. Save the exact failing compile command and source file.
2. Rerun the same compile with `../dev/cppgm++` and with the `*-self` compiler.
3. If only `*-self` fails, find where the self compiler differs from the
   host-seeded compiler. Narrow that to the self-built source file or object
   whose generated code changes behavior.
4. Reduce the construct that made `../dev/cppgm++` miscompile that compiler
   source file.
5. Add that reducer to the earliest owning PA and fix the underlying compiler
   bug.

Failure includes severe performance divergence. A self-built compiler is
expected to be slower than the host-seeded compiler, but not wildly slower. If a
`*-self` or `*-inception` compile is more than about five times slower than the
same source under `../dev/cppgm++`, or times out while the host-seeded compiler
completes, treat that as possible miscompilation of the compiler itself.
Compare the layers and trace the slowdown back to the self-built object, source
file, or compiler feature that introduced the divergent behavior.

A stack trace or assertion inside the self-built compiler identifies where the
bad program failed; it does not by itself prove that the code at that stack
frame is the source bug. First decide whether regular `../dev/cppgm++` has the
same failure or whether the self-built compiler diverged because one of its own
objects was miscompiled.

If both compilers build the source but the outputs differ, reduce the first
different artifact. For a binary mismatch, compare at the earliest useful
boundary: generated LowIR, object metadata, symbols, relocations, section
contents, or linked output. A byte mismatch is not a PA39 feature request; it
is usually an earlier lowering, backend, ordering, path, timestamp, or
configuration determinism bug.

Do not:

- add PA39-only behavior to make a checkpoint move forward
- rewrite tests or references around an inception failure
- skip work by substituting a custom implementation for compiler source or
  hosted header behavior
- replace the fixed checkpoint source sets with a generated source scan
- increase timeouts before reducing the performance or nontermination bug

### Useful Targets

The main goal is:

```sh
make cppgm++-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
make compare-cppgm++-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
```

Useful broader targets are:

```sh
make inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
make compare-inception CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
make bitcmp CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
```

During a normal in-tree inception build, PA39 also checks each newly built
inception object before the final target link finishes. The check byte-compares
the new inception `.o` against the corresponding self-host `.o` and stops at
the first mismatch. The restored-self diagnostic target disables this object
check because it may not have a matching self-host object tree.

The compile wrapper also applies a default per-command RSS cap. By default,
commands that exceed 8 GiB RSS fail with `EXIT_OOM`; set
`CPPGM_RUN_MAX_RSS_KB=0` to disable that guard for diagnosis. The initial
`*-self` build uses normal make parallelism; the `*-inception` subbuild is
capped separately by `INCEPTION_BUILD_JOBS`, which defaults to at most 8 jobs.

Useful checkpoint targets are:

```sh
make pptoken-self CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
make cppgm++-self CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
make through-cppgm++ CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
```

Useful preservation targets are:

```sh
make test-through-pa9 CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
make test-through-pa38 CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
make test-pa10 CXX=../dev/cppgm++ CPPGM_HOST_CXX=g++
```

The `test-through-*` ladder is a debugging aid, not the final product. Each
rung runs already-completed assignment tests with the appropriate self-built
checkpoint so failures appear closer to the stage that first needs the missing
behavior.

### Single-Object Probes

During PA39, changing one `dev/src/*.cpp` file and then rerunning a canonical
self-host target can rebuild every self-host object. That rebuild is correct:
the object files depend on the compiler binary that produced them, and mixing
objects from different compiler generations would make the inception result
untrustworthy.

For quick iteration, use a scratch object probe instead:

```sh
make probe-self-object SOURCE=../dev/src/semantic_output.cpp
make probe-self-object SOURCE=dev/src/semantic_output.cpp
make probe-self-object SOURCE=../dev/cppgm++.cpp
```

The probe uses the PA39 self-host compile flags and timeout, but writes to
`../obj/pa39/probe/selfhost/...` instead of the canonical
`../obj/pa39/selfhost/...` tree. It prints the compiler, source, object, and
depfile paths. By default it uses `PROBE_CXX=../dev/cppgm++`; set `PROBE_CXX`
if you need to test a different compiler binary.

If the canonical checkpoint objects already exist, you can link one scratch
replacement object into a scratch binary:

```sh
make probe-self-link SOURCE=../dev/src/semantic_output.cpp PROBE_TARGET=cppgm++
```

`probe-self-link` refuses to link if the probed object is not part of
`PROBE_TARGET`, or if any required canonical object is missing. This keeps the
probe from silently becoming a mixed or incomplete build. Probe targets are
only for diagnosis; final validation still requires the canonical PA39 targets.

### Checkpoint Ownership

The checkpoint used for each assignment stage is:

- `pptoken-self`: PA1
- `posttoken-self`: PA2
- `ctrlexpr-self`: PA3
- `macro-self`: PA4
- `preproc-self`: PA5
- `recog-self`: PA6
- `nsdecl-self`: PA7
- `nsinit-self`: PA8
- `cy86-self`: PA9
- `cppgm++-self`: PA10-PA12, PA14-PA27, and PA29-PA36
- `lowir2cy86-self`: PA13
- `lowir2native-self`: PA28 and PA38
- `abimangle-self`: PA30
- `lowiropt-self`: PA37

Checkpoint source sets are fixed by `../dev/frontend_source_sets.mk`. PA39 is
checking whether those known implementation source sets can be rebuilt
reproducibly.

### Build Variables And Timeouts

Use:

- `CXX=../dev/cppgm++` to select the course compiler under test.
- `CPPGM_HOST_CXX=<host-cxx>` to select the host compiler used for linking
  checkpoint programs and generating hosted compiler configuration.

PA39 applies per-file wall timeouts so one compile cannot stall indefinitely:

- `INCEPTION_SELFHOST_COMPILE_TIMEOUT_SEC=900` for `*-self` object compiles
- `INCEPTION_INCEPTION_COMPILE_TIMEOUT_SEC=3600` for `*-inception` object
  compiles

A timeout means the current compiler is too slow or stuck on that source file.
If the timeout happens only in a self-built layer, first compare against the
host-seeded compiler. A moderate slowdown is expected, but a severe slowdown is
divergence to trace through the self compiler build. Then reduce the source and
fix the owning earlier compiler surface instead of treating the timeout as a
PA39-specific condition.
