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
with tuple_pattern_eq_dec : forall (p1 p2 : tuple_pattern), {p1 = p2} + {p1 <> p2}
with record_pattern_eq_dec : forall (p1 p2 : record_pattern), {p1 = p2} + {p1 <> p2}
with variant_pattern_eq_dec : forall (p1 p2 : variant_pattern), {p1 = p2} + {p1 <> p2}.
Proof. all: decide equality; auto with eq_dec_db. Defined.

Hint Resolve pattern_eq_dec : eq_dec_db.
Hint Resolve tuple_pattern_eq_dec : eq_dec_db.
Hint Resolve record_pattern_eq_dec : eq_dec_db.
Hint Resolve variant_pattern_eq_dec : eq_dec_db.

Lemma op1_eq_dec : forall (op1 op2 : op1), {op1 = op2} + {op1 <> op2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Lemma op2_eq_dec : forall (op1 op2 : op2), {op1 = op2} + {op1 <> op2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Lemma for_direction_eq_dec : forall (d1 d2 : for_direction), {d1 = d2} + {d1 <> d2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Hint Resolve op1_eq_dec : eq_dec_db.
Hint Resolve op2_eq_dec : eq_dec_db.
Hint Resolve for_direction_eq_dec : eq_dec_db.

Lemma comp_eq_dec : forall (t1 t2 : comp), {t1 = t2} + {t1 <> t2}
with expr_eq_dec : forall (t1 t2 : expr), {t1 = t2} + {t1 <> t2}
with ret_term_eq_dec : forall (t1 t2 : ret_term), {t1 = t2} + {t1 <> t2}
with exn_term_eq_dec : forall (t1 t2 : exn_term), {t1 = t2} + {t1 <> t2}
with eff_term_eq_dec : forall (t1 t2 : eff_term), {t1 = t2} + {t1 <> t2}
with match_term_eq_dec : forall (t1 t2 : match_term), {t1 = t2} + {t1 <> t2}
with tuple_expr_eq_dec : forall (t1 t2 : tuple_expr), {t1 = t2} + {t1 <> t2}
with record_expr_eq_dec : forall (t1 t2 : record_expr), {t1 = t2} + {t1 <> t2}
with variant_expr_eq_dec : forall (t1 t2 : variant_expr), {t1 = t2} + {t1 <> t2}
with fix_mut_term_eq_dec : forall (t1 t2 : fix_mut_term), {t1 = t2} + {t1 <> t2}
with array_expr_eq_dec : forall (t1 t2 : array_expr), {t1 = t2} + {t1 <> t2}.
Proof. all: decide equality; auto with eq_dec_db. Defined.

Hint Resolve comp_eq_dec : eq_dec_db.
Hint Resolve expr_eq_dec : eq_dec_db.
Hint Resolve ret_term_eq_dec : eq_dec_db.
Hint Resolve exn_term_eq_dec : eq_dec_db.
Hint Resolve eff_term_eq_dec : eq_dec_db.
Hint Resolve match_term_eq_dec : eq_dec_db.
Hint Resolve tuple_expr_eq_dec : eq_dec_db.
Hint Resolve record_expr_eq_dec : eq_dec_db.
Hint Resolve variant_expr_eq_dec : eq_dec_db.
Hint Resolve fix_mut_term_eq_dec : eq_dec_db.

Lemma val_eq_dec : forall (v1 v2 : val), {v1 = v2} + {v1 <> v2}
with kont_eq_dec : forall (k1 k2 : kont), {k1 = k2} + {k1 <> k2}
with metakont_eq_dec : forall (mk1 mk2 : metakont), {mk1 = mk2} + {mk1 <> mk2}
with env_eq_dec : forall (e1 e2 : env), {e1 = e2} + {e1 <> e2}
with tuple_eq_dec : forall (t1 t2 : tuple), {t1 = t2} + {t1 <> t2}
with record_eq_dec : forall (r1 r2 : record), {r1 = r2} + {r1 <> r2}
with variant_eq_dec : forall (v1 v2 : variant), {v1 = v2} + {v1 <> v2}.
Proof. all: decide equality; auto with eq_dec_db. Defined.

Hint Resolve val_eq_dec : eq_dec_db.
Hint Resolve kont_eq_dec : eq_dec_db.
Hint Resolve metakont_eq_dec : eq_dec_db.
Hint Resolve env_eq_dec : eq_dec_db.
Hint Resolve tuple_eq_dec : eq_dec_db.
Hint Resolve record_eq_dec : eq_dec_db.
Hint Resolve variant_eq_dec : eq_dec_db.

Lemma applicable_eq_dec : forall (a1 a2 : applicable), {a1 = a2} + {a1 <> a2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Lemma array_eq_dec : forall (a1 a2 : array), {a1 = a2} + {a1 <> a2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Hint Resolve applicable_eq_dec : eq_dec_db.
Hint Resolve array_eq_dec : eq_dec_db.
