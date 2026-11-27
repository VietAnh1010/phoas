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

Constructors in `syntax.v` start with their type's prefix:

| Prefix | Type | Prefix | Type |
|---|---|---|---|
| `B` | `binder` | `V` | `val` |
| `P` | `pattern` | `K` | `kont` |
| `C` | `comp` | `MK` | `metakont` |
| `E` | `expr` | `A` | `applicable` |

Other types:

| Type | Prefix | Example |
|---|---|---|
| List of a type above | its prefix plus `s` | `PsNil` (`patterns`) |
| `<word>_<type above>` | its prefix plus the word | `PRecordNil` (`record_pattern`) |
| Any other type | the type name in CamelCase | `EnvNil` (`env`), `UnOpNeg` (`un_op`) |

Exceptions: `FixMut` for `fix_mut_defs`, and OCaml's `Upto` and `Downto`.

Variables are named after their type:

| Type | Name | Example |
|---|---|---|
| A type above, or `<word>_<type above>` | its prefix in lowercase | `c : comp`, `p : record_pattern` |
| Any other type | the initial of the last word | `c : return_case` |
| Type named by a plural noun | the last word's initial plus `s` | `es : exprs`, `ds : fix_mut_defs` |
| `ident` | its role | `x` variable, `f` function, `l` label or primitive |
| Variable in a notation whose custom entry accepts more than one type | the entry's initial | `t` (entry `term`) |

Another name may replace an unclear or clashing default from the table
(`op : un_op`, `rho : env` in a file with `expr` variables). One name may be
used for several types (`v` for `val` and `variant`). Number a name only when
one clause would bind it twice (`PRecordCons l p1 p2`, but
`RecordNil, RecordCons l _ _`).

A new value for a name in scope keeps the name when it updates an old value
that is no longer used: the environment after a match, the heap after a write,
or an inner `fix` parameter (`go i t`). Otherwise it takes a prime: a subterm
(`VsCons v vs'`), a new meaning (`Some v'`, read from the reference `v`), or an
update whose old value is still used (`let i' := f i`). Exception: a subterm in
a `positive` pattern keeps the name (`p1~0 => reverse_append p1 p2~0`).

A lemma stating the equation of one clause of a function is named
`fold_unfold_<function>_<constructors>`, constructors in match order
(`fold_unfold_match_pattern_PPair_VPair`).

## Code style

- Imports: `From` lines grouped by package in the order `Stdlib`,
  `shift_reset.lib`, `shift_reset.core`, `shift_reset.monad`,
  `shift_reset.interpreter`. Within a package, plain `Require` before
  `Require Import`, and `syntax` first among `shift_reset.core` modules.
- Monadic map: `f <$> m` for a named function (`VBool <$> equal_val v1 v2`),
  and `let+` for a lambda (`let+ b := equal_val v1 v2 in VBool (negb b)`).
- Binds: a chain nests to the right with `let*`, never `m >>= f >>= g`. A
  single `m >>= f` is fine.

## Datatype design

Rules for `shift-reset/core/syntax.v`:

- Sequences: use a monomorphic list type, not `list T`. Name it `T` plus `s`
  (`exprs`, `vals`) if its constructors are only Nil and a Cons of one `T` and
  the tail, with no invariant. Otherwise give it its own name: `cases` (Cons
  takes a `pattern` and a `comp`), `record_expr` (also has `ERecordRest` and
  `ERecordConsPun`), `record` (sorted, distinct labels).
- Share: constructs whose types would have identical constructors and
  invariants use one type (`cases` for `CMatch` and `CTry`).
- Split: different invariants need separate types, even with identical
  constructors (`env` allows shadowed keys, `record` has sorted, distinct
  labels).
- Order: parallel types (`pattern`, `expr`, `val`) list corresponding
  constructors in the same order, since constructor order affects printing.
- Alias: `Definition X := T` names a role of `T` in signatures (`match_cases`,
  `try_cases`). An alias is convertible with `T`, so Rocq accepts a
  `try_cases` where a `match_cases` is expected.

### Views

A view is the type `X` in `val_to_<construct> : val -> option X` (`val.v`),
the function that unwraps one kind of `val`.

- Plain: the view is the type `T` of the data that the `val` constructor
  carries, when `T` denotes the construct (`Z` for ints, `val * val` for
  pairs, `loc` for refs).
- Wrapper: otherwise the view is a one-constructor `Inductive` whose
  constructor takes the arguments of the `val` constructor
  (`Tuple : vals -> tuple`, as `vals` is a list, not a tuple, and
  `Variant : ident -> val -> variant`, as `ident * val` is a pair, not a
  variant).
- Each view is chosen on its own: `Z` is the plain view for ints, even though
  array lengths are also `Z`.
