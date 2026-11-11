From Stdlib Require Import Arith Ascii String Qcanon ZArith.
From shift_reset.core Require Import syntax ident loc.

Create HintDb eq_dec_db discriminated.

Hint Resolve ascii_dec : eq_dec_db.
Hint Resolve string_dec : eq_dec_db.
Hint Resolve Nat.eq_dec : eq_dec_db.
Hint Resolve Z.eq_dec : eq_dec_db.
Hint Resolve Qc_eq_dec : eq_dec_db.
Hint Resolve ident_eq_dec : eq_dec_db.
Hint Resolve loc_eq_dec : eq_dec_db.

Lemma binder_eq_dec : forall (b1 b2 : binder), {b1 = b2} + {b1 <> b2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Hint Resolve binder_eq_dec : eq_dec_db.

Lemma pattern_eq_dec : forall (p1 p2 : pattern), {p1 = p2} + {p1 <> p2}
with patterns_eq_dec : forall (ps1 ps2 : patterns), {ps1 = ps2} + {ps1 <> ps2}
with record_pattern_eq_dec : forall (p1 p2 : record_pattern), {p1 = p2} + {p1 <> p2}.
Proof. all: decide equality; auto with eq_dec_db. Defined.

Hint Resolve pattern_eq_dec : eq_dec_db.
Hint Resolve patterns_eq_dec : eq_dec_db.
Hint Resolve record_pattern_eq_dec : eq_dec_db.

Lemma un_op_eq_dec : forall (op1 op2 : un_op), {op1 = op2} + {op1 <> op2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Lemma bin_op_eq_dec : forall (op1 op2 : bin_op), {op1 = op2} + {op1 <> op2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Lemma direction_flag_eq_dec : forall (d1 d2 : direction_flag), {d1 = d2} + {d1 <> d2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Hint Resolve un_op_eq_dec : eq_dec_db.
Hint Resolve bin_op_eq_dec : eq_dec_db.
Hint Resolve direction_flag_eq_dec : eq_dec_db.

Lemma comp_eq_dec : forall (c1 c2 : comp), {c1 = c2} + {c1 <> c2}
with expr_eq_dec : forall (e1 e2 : expr), {e1 = e2} + {e1 <> e2}
with cases_eq_dec : forall (cs1 cs2 : cases), {cs1 = cs2} + {cs1 <> cs2}
with handle_cases_eq_dec : forall (cs1 cs2 : handle_cases), {cs1 = cs2} + {cs1 <> cs2}
with return_case_eq_dec : forall (c1 c2 : return_case), {c1 = c2} + {c1 <> c2}
with effect_cases_eq_dec : forall (cs1 cs2 : effect_cases), {cs1 = cs2} + {cs1 <> cs2}
with fix_mut_defs_eq_dec : forall (ds1 ds2 : fix_mut_defs), {ds1 = ds2} + {ds1 <> ds2}
with exprs_eq_dec : forall (es1 es2 : exprs), {es1 = es2} + {es1 <> es2}
with record_expr_eq_dec : forall (e1 e2 : record_expr), {e1 = e2} + {e1 <> e2}.
Proof. all: decide equality; auto with eq_dec_db. Defined.

Hint Resolve comp_eq_dec : eq_dec_db.
Hint Resolve expr_eq_dec : eq_dec_db.
Hint Resolve cases_eq_dec : eq_dec_db.
Hint Resolve handle_cases_eq_dec : eq_dec_db.
Hint Resolve effect_cases_eq_dec : eq_dec_db.
Hint Resolve return_case_eq_dec : eq_dec_db.
Hint Resolve fix_mut_defs_eq_dec : eq_dec_db.
Hint Resolve exprs_eq_dec : eq_dec_db.
Hint Resolve record_expr_eq_dec : eq_dec_db.

Lemma val_eq_dec : forall (v1 v2 : val), {v1 = v2} + {v1 <> v2}
with kont_eq_dec : forall (k1 k2 : kont), {k1 = k2} + {k1 <> k2}
with metakont_eq_dec : forall (mk1 mk2 : metakont), {mk1 = mk2} + {mk1 <> mk2}
with vals_eq_dec : forall (vs1 vs2 : vals), {vs1 = vs2} + {vs1 <> vs2}
with env_eq_dec : forall (e1 e2 : env), {e1 = e2} + {e1 <> e2}
with record_eq_dec : forall (r1 r2 : record), {r1 = r2} + {r1 <> r2}.
Proof. all: decide equality; auto with eq_dec_db. Defined.

Hint Resolve val_eq_dec : eq_dec_db.
Hint Resolve kont_eq_dec : eq_dec_db.
Hint Resolve metakont_eq_dec : eq_dec_db.
Hint Resolve vals_eq_dec : eq_dec_db.
Hint Resolve env_eq_dec : eq_dec_db.
Hint Resolve record_eq_dec : eq_dec_db.

Lemma tuple_eq_dec : forall (t1 t2 : tuple), {t1 = t2} + {t1 <> t2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Lemma variant_eq_dec : forall (v1 v2 : variant), {v1 = v2} + {v1 <> v2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Lemma enum_eq_dec : forall (e1 e2 : enum), {e1 = e2} + {e1 <> e2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Lemma array_eq_dec : forall (a1 a2 : array), {a1 = a2} + {a1 <> a2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Lemma applicable_eq_dec : forall (a1 a2 : applicable), {a1 = a2} + {a1 <> a2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Hint Resolve tuple_eq_dec : eq_dec_db.
Hint Resolve variant_eq_dec : eq_dec_db.
Hint Resolve enum_eq_dec : eq_dec_db.
Hint Resolve array_eq_dec : eq_dec_db.
Hint Resolve applicable_eq_dec : eq_dec_db.
