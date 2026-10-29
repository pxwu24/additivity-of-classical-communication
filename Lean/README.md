# Lean Formalization

This directory is the complete Lean project accompanying the manuscript. The public Lean namespace remains `SchurEntropy`; all sources, pinned dependencies, build configuration, and audit tooling are contained here.

## Build and audit

From the repository root, run:

```sh
cd Lean
lake exe cache get
./scripts/check.sh
```

The check script also works when invoked as `./Lean/scripts/check.sh` from the repository root. It builds the project and audits the transitive axioms of every imported `SchurEntropy` declaration.

- [Lean Formalization](verification.md): numbered manuscript results, exact theorem scope, and audit details.
- [Source organization](SchurEntropy/README.md): modules and proof dependencies.
- [Result imports](SchurEntropy.lean): the full collection of verified results.
- [Audit](Audit.lean): exported type checks and axiom audit.
- [Mathematical proofs](../Proofs/README.md): readable proofs arranged by the manuscript's result numbers.
- [Source attribution](third_party/NOTICE): adapted components and dependency licenses.

The dependency versions in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` are unchanged by this directory reorganization.
