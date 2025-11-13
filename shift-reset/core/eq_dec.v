From Stdlib Require Import Qcanon ZArith.
From shift_reset.core Require Import syntax loc tag var.

Create HintDb eq_dec_db discriminated.

Hint Resolve Z.eq_dec : eq_dec_db.
Hint Resolve Qc_eq_dec : eq_dec_db.
Hint Resolve loc_eq_dec : eq_dec_db.
Hint Resolve tag_eq_dec : eq_dec_db.
Hint Resolve var_eq_dec : eq_dec_db.

Lemma binder_eq_dec : forall (b1 b2 : binder), {b1 = b2} + {b1 <> b2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Hint Resolve binder_eq_dec : eq_dec_db.

Lemma variant_pattern_eq_dec : forall (p1 p2 : variant_pattern), {p1 = p2} + {p1 <> p2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Lemma tuple_pattern_eq_dec : forall (p1 p2 : tuple_pattern), {p1 = p2} + {p1 <> p2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Lemma record_pattern_eq_dec : forall (p1 p2 : record_pattern), {p1 = p2} + {p1 <> p2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Hint Resolve variant_pattern_eq_dec : eq_dec_db.
Hint Resolve tuple_pattern_eq_dec : eq_dec_db.
Hint Resolve record_pattern_eq_dec : eq_dec_db.

Lemma op1_eq_dec : forall (op1 op2 : op1), {op1 = op2} + {op1 <> op2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Lemma op2_eq_dec : forall (op1 op2 : op2), {op1 = op2} + {op1 <> op2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Hint Resolve op1_eq_dec : eq_dec_db.
Hint Resolve op2_eq_dec : eq_dec_db.

Lemma term_eq_dec : forall (t1 t2 : term), {t1 = t2} + {t1 <> t2}
with val_term_eq_dec : forall (t1 t2 : val_term), {t1 = t2} + {t1 <> t2}
with ret_term_eq_dec : forall (t1 t2 : ret_term), {t1 = t2} + {t1 <> t2}
with exn_term_eq_dec : forall (t1 t2 : exn_term), {t1 = t2} + {t1 <> t2}
with eff_term_eq_dec : forall (t1 t2 : eff_term), {t1 = t2} + {t1 <> t2}
with variant_term_eq_dec : forall (t1 t2 : variant_term), {t1 = t2} + {t1 <> t2}
with tuple_term_eq_dec : forall (t1 t2 : tuple_term), {t1 = t2} + {t1 <> t2}
with record_term_eq_dec : forall (t1 t2 : record_term), {t1 = t2} + {t1 <> t2}
with fix_mut_term_eq_dec : forall (t1 t2 : fix_mut_term), {t1 = t2} + {t1 <> t2}.
Proof. all: decide equality; auto with eq_dec_db. Defined.

Hint Resolve term_eq_dec : eq_dec_db.
Hint Resolve val_term_eq_dec : eq_dec_db.
Hint Resolve ret_term_eq_dec : eq_dec_db.
Hint Resolve exn_term_eq_dec : eq_dec_db.
Hint Resolve eff_term_eq_dec : eq_dec_db.
Hint Resolve variant_term_eq_dec : eq_dec_db.
Hint Resolve tuple_term_eq_dec : eq_dec_db.
Hint Resolve record_term_eq_dec : eq_dec_db.
Hint Resolve fix_mut_term_eq_dec : eq_dec_db.

Lemma val_eq_dec : forall (v1 v2 : val), {v1 = v2} + {v1 <> v2}
with kont_eq_dec : forall (k1 k2 : kont), {k1 = k2} + {k1 <> k2}
with metakont_eq_dec : forall (mk1 mk2 : metakont), {mk1 = mk2} + {mk1 <> mk2}
with env_eq_dec : forall (e1 e2 : env), {e1 = e2} + {e1 <> e2}
with tuple_eq_dec : forall (t1 t2 : tuple), {t1 = t2} + {t1 <> t2}
with record_eq_dec : forall (r1 r2 : record), {r1 = r2} + {r1 <> r2}.
Proof. all: decide equality; auto with eq_dec_db. Defined.

Hint Resolve val_eq_dec : eq_dec_db.
Hint Resolve kont_eq_dec : eq_dec_db.
Hint Resolve metakont_eq_dec : eq_dec_db.
Hint Resolve env_eq_dec : eq_dec_db.
Hint Resolve tuple_eq_dec : eq_dec_db.
Hint Resolve record_eq_dec : eq_dec_db.

Lemma closure_eq_dec : forall (c1 c2 : closure), {c1 = c2} + {c1 <> c2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Lemma variant_eq_dec : forall (v1 v2 : variant), {v1 = v2} + {v1 <> v2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Lemma exn_eq_dec : forall (e1 e2 : exn), {e1 = e2} + {e1 <> e2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Lemma eff_eq_dec : forall (e1 e2 : eff), {e1 = e2} + {e1 <> e2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Hint Resolve closure_eq_dec : eq_dec_db.
Hint Resolve variant_eq_dec : eq_dec_db.
Hint Resolve exn_eq_dec : eq_dec_db.
Hint Resolve eff_eq_dec : eq_dec_db.
