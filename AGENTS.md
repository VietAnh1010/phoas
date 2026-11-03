# Project instructions

A Rocq formalization of a call-by-value language with delimited control
operators, deep and shallow algebraic effect handlers, and exceptions. It
contains a definitional interpreter (`shift-reset/interpreter`), a monad
library with its laws (`shift-reset/monad/`, `proofs/monad/`), and example
programs (`examples/`).

## Writing style

- Never use long dashes. No en-dash (–) and no em-dash (—). Always use a plain
  hyphen (-) instead. This applies to code, comments, and Markdown files.
- Use precise language. Prefer exact terms from programming languages and logic
  (for example "codomain", "convertible", "vacuous", "unsatisfiable") over loose
  or metaphorical verbs (for example "feed", "land in", "sidestep", "cover").

## Naming

- Name the equational lemma for one clause of a `Fixpoint`/`Definition`
  `fold_unfold_<function>_<constructor>`, listing the scrutinized constructors
  in match order (for example `fold_unfold_match_pattern_PPair_VPair`,
  `fold_unfold_interpret_tuple_term_TTupleNil`).
