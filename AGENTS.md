# Project instructions

A Rocq formalization of a call-by-value language with delimited control
operators, deep and shallow algebraic effect handlers, and exceptions.

- `shift-reset/interpreter/`: definitional interpreter
- `shift-reset/monad/`, `proofs/monad/`: monad library and its laws
- `examples/`: example programs

## Writing style

- Use a plain hyphen (-), never an en or em dash.
- Use exact terms ("codomain", "convertible"), not metaphors ("feed", "land
  in").

## Naming

- Constructors: derive the name from the type name (`PsNil`, `EnvNil`), except
  OCaml's `Upto` and `Downto`.
- Lemmas: name the equation for one clause
  `fold_unfold_<function>_<constructors>`, with constructors in match order
  (`fold_unfold_match_pattern_PPair_VPair`).

## Datatype design

These rules govern `shift-reset/core/syntax.v`.

- Sequences: define a monomorphic list type of `T`s instead of `list T`. Give
  it a generic name (`exprs`, `vals`) unless it has its own constructors or
  invariants (`record`).
- Share: constructs whose types would have identical constructors and
  invariants use one type (`cases` for `CMatch` and `CTry`).
- Split: use separate types when invariants differ, even with identical
  constructors (`env` allows shadowed keys, `record` has sorted, distinct
  labels).
- Order: parallel types (`pattern`, `expr`, `val`) list corresponding
  constructors in the same order, since constructor order affects printing.
- Alias: `Definition X := T` names a role of `T` in signatures (`match_cases`,
  `try_cases`). Rocq does not check aliases.

### Views

A view is the codomain of a function that unwraps one kind of `val`. Below,
`T` is the type of the data that the `val` constructor carries.

- Plain: the view is `T` when `T` has the meaning of the construct (`Z` for
  ints, `val * val` for pairs, `loc` for refs).
- Wrapper: the view is `Inductive X := C : T -> X` when `T` only stores the
  construct's data (`vals` is not a tuple, so `tuple` wraps it).
- Other uses of `T` do not matter: `Z` also denotes array lengths.
