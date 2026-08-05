# Contributing

## Before coding

1. Read `STATUS.md`, `docs/ROADMAP.md`, and the relevant architecture section.
2. Search Mathlib and pinned upstream dependencies for existing declarations.
3. Open an issue for changes that alter conventions or public abstractions.

## Development loop

```sh
lake build YangMills.Path.To.ChangedModule
lake build
rg -n '\bsorry\b|\badmit\b' YangMills
```

Keep commits focused on one milestone-sized result. Add a docstring to every
mathematically nontrivial public declaration and a small executable example for
every major abstraction.

## Pull requests

A pull request should state:

- the paper-level result and its Lean declarations;
- exact assumptions and conventions;
- whether code is imported, adapted, generalized, or original;
- commands used to verify it;
- remaining blockers without weakening the advertised theorem.

No proof placeholders, project axioms, or unsafe proof shortcuts are accepted.
