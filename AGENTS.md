# Project instructions

A Rocq formalization of a call-by-value language with delimited control
operators, deep and shallow algebraic effect handlers, and exceptions.

- `shift-reset/core/`: syntax and values (`syntax.v`), notations
  (`syntax_notation.v`)
- `shift-reset/interpreter/`: definitional interpreter
- `shift-reset/monad/`, `proofs/monad/`: monad library and its laws
- `examples/`: example programs

## Writing style

- Use a plain hyphen (-), never an en or em dash.
- Use exact terms ("codomain", "convertible"), not metaphors ("feed", "land
  in").

## Naming

The constructors of these types in `syntax.v` start with a prefix:

| Prefix | Type | Prefix | Type |
|---|---|---|---|
| `B` | `binder` | `V` | `val` |
| `P` | `pattern` | `K` | `kont` |
| `C` | `comp` | `MK` | `metakont` |
| `E` | `expr` | `A` | `applicable` |

Other types prefix their constructors as follows:

| Type | Prefix | Example |
|---|---|---|
| List of a type above | its prefix plus `s` | `PsNil`, `PsCons` (`patterns`) |
| `<word>_<type above>` | its prefix plus the word | `PRecordNil` (`record_pattern`), `ERecordNil` (`record_expr`) |
| Any other type | the type name in CamelCase | `EnvNil` (`env`), `UnOpNeg` (`un_op`) |

Exceptions: `fix_mut_defs` uses `FixMut`, not `FixMutDefs`. OCaml's `Upto` and
`Downto` keep their names.

Variables are named after their type:

| Type | Name | Example |
|---|---|---|
| A type above | its prefix in lowercase | `c : comp`, `mk : metakont` |
| `<word>_<type above>` | its prefix in lowercase | `p : record_pattern` |
| Any other type | the initial of the last word | `c : return_case` |
| Type named by a plural noun | the initial of the last word, singular, plus `s` | `es : exprs`, `ds : fix_mut_defs` |
| `ident` | its role | `x` variable, `f` function, `l` label or primitive |
| Variable in a notation whose custom entry accepts more than one type | the entry's initial | `t` (entry `term`) |

Exceptions: `op : un_op`, `op : bin_op`, `d : direction_flag`.
Number repeated names in one clause: `PRecordCons l p1 p2`. One name may serve
several types (`v` for `val` and `variant`).

Lemmas: a lemma that states the equation for one clause of a function is
named `fold_unfold_<function>_<constructors>`, with the constructors in match
order (`fold_unfold_match_pattern_PPair_VPair`).

## Datatype design

These rules govern `shift-reset/core/syntax.v`.

- Sequences: define a monomorphic list type instead of `list T`. If its only
  constructors are Nil and a Cons that takes one `T` and the tail, and it has
  no invariant, name it `T` plus `s` (`exprs`, `vals`). Otherwise give it its
  own name: `cases` (its Cons takes a `pattern` and a `comp`), `record_expr`
  (it also has `ERecordRest` and `ERecordConsPun`), `record` (sorted, distinct
  labels).
- Share: constructs whose types would have identical constructors and
  invariants use one type (`cases` for `CMatch` and `CTry`).
- Split: use separate types when invariants differ, even with identical
  constructors (`env` allows shadowed keys, `record` has sorted, distinct
  labels).
- Order: parallel types (`pattern`, `expr`, `val`) list corresponding
  constructors in the same order, since constructor order affects printing.
- Alias: `Definition X := T` names a role of `T` in signatures (`match_cases`,
  `try_cases`). An alias is convertible with `T`, so Rocq accepts a `try_cases`
  where a `match_cases` is expected.

### Views

A view is the type `X` in `val_to_<construct> : val -> option X` (in `val.v`),
the function that unwraps one kind of `val`. Below, `T` is the type of the
data that the `val` constructor carries.

- Plain: the view is `T` when `T` itself denotes the construct (`Z` for ints,
  `val * val` for pairs, `loc` for refs).
- Wrapper: otherwise the view is a one-constructor `Inductive` whose
  constructor takes the same arguments as the `val` constructor
  (`Tuple : vals -> tuple`, since `vals` is a list, not a tuple;
  `Variant : ident -> val -> variant`, since `ident * val` is a pair, not a
  variant).
- Choose each view on its own: `Z` is the plain view for ints, even though
  array lengths are also `Z`.
