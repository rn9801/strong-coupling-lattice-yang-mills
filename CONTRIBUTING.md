# Contributing

## Before coding

1. Read `STATUS.md`, `docs/ARCHITECTURE.md`, and the relevant module
   documentation.
2. Search Mathlib and pinned upstream dependencies for existing declarations.
3. Open an issue for changes that alter conventions or public abstractions.

## Development loop

```sh
lake build YangMills.Path.To.ChangedModule
lake build
lake build +YangMills.Regression
rg -n '\bsorry\b|\badmit\b' YangMills
```

The first two commands are the ordinary edit loop.  The opt-in regression root
also compiles the complete theorem and axiom-audit suite, the pinned Douglas
baseline, and the older Dobrushin comparison branch; run it before merging
changes to shared infrastructure or preparing a release.

Keep commits focused on one coherent result. Add a docstring to every
mathematically nontrivial public declaration and a small executable example
for every major abstraction.

## Pull requests

A pull request should state:

- the paper-level result and its Lean declarations;
- exact assumptions and conventions;
- whether code is imported, adapted, generalized, or original;
- commands used to verify it;
- remaining blockers without weakening the advertised theorem.

No proof placeholders, project axioms, or unsafe proof shortcuts are accepted.
