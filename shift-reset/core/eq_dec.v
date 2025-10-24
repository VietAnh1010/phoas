From Stdlib Require Import Bool Qcanon ZArith.
From shift_reset.core Require Import syntax loc tag var.

Create HintDb eq_dec_db discriminated.

Hint Resolve Z.eq_dec : eq_dec_db.
Hint Resolve Qc_eq_dec : eq_dec_db.
Hint Resolve bool_dec : eq_dec_db.
Hint Resolve loc_eq_dec : eq_dec_db.
Hint Resolve tag_eq_dec : eq_dec_db.
Hint Resolve var_eq_dec : eq_dec_db.

Lemma binder_eq_dec : forall (b1 b2 : binder), {b1 = b2} + {b1 <> b2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Hint Resolve binder_eq_dec : eq_dec_db.

Lemma pattern_eq_dec : forall (p1 p2 : pattern), {p1 = p2} + {p1 <> p2}.
Proof. decide equality; auto with eq_dec_db. Defined.

Hint Resolve pattern_eq_dec : eq_dec_db.

Lemma term_eq_dec : forall (t1 t2 : term), {t1 = t2} + {t1 <> t2}
with val_term_eq_dec : forall (t1 t2 : val_term), {t1 = t2} + {t1 <> t2}
with term1_eq_dec : forall (t1 t2 : term1), {t1 = t2} + {t1 <> t2}
with term2_eq_dec : forall (t1 t2 : term2), {t1 = t2} + {t1 <> t2}
with ret_term_eq_dec : forall (t1 t2 : ret_term), {t1 = t2} + {t1 <> t2}
with exn_term_eq_dec : forall (t1 t2 : exn_term), {t1 = t2} + {t1 <> t2}
with eff_term_eq_dec : forall (t1 t2 : eff_term), {t1 = t2} + {t1 <> t2}.
Proof. all: decide equality; auto with eq_dec_db. Defined.

Hint Resolve term_eq_dec : eq_dec_db.
Hint Resolve val_term_eq_dec : eq_dec_db.
Hint Resolve term1_eq_dec : eq_dec_db.
Hint Resolve term2_eq_dec : eq_dec_db.
Hint Resolve ret_term_eq_dec : eq_dec_db.
Hint Resolve exn_term_eq_dec : eq_dec_db.
Hint Resolve eff_term_eq_dec : eq_dec_db.

Lemma val_eq_dec : forall (v1 v2 : val), {v1 = v2} + {v1 <> v2}
with fun_clo_eq_dec : forall (c1 c2 : fun_clo), {c1 = c2} + {c1 <> c2}
with fix_clo_eq_dec : forall (c1 c2 : fix_clo), {c1 = c2} + {c1 <> c2}
with kont_clo_eq_dec : forall (c1 c2 : kont_clo), {c1 = c2} + {c1 <> c2}
with try_clo_eq_dec : forall (c1 c2 : try_clo), {c1 = c2} + {c1 <> c2}
with handle_clo_eq_dec : forall (c1 c2 : handle_clo), {c1 = c2} + {c1 <> c2}
with shallow_handle_clo_eq_dec : forall (c1 c2 : shallow_handle_clo), {c1 = c2} + {c1 <> c2}
with kont_eq_dec : forall (k1 k2 : kont), {k1 = k2} + {k1 <> k2}
with metakont_eq_dec : forall (mk1 mk2 : metakont), {mk1 = mk2} + {mk1 <> mk2}
with env_eq_dec : forall (env1 env2 : env), {env1 = env2} + {env1 <> env2}
with exn_eq_dec : forall (exn1 exn2 : exn), {exn1 = exn2} + {exn1 <> exn2}
with eff_eq_dec : forall (eff1 eff2 : eff), {eff1 = eff2} + {eff1 <> eff2}.
Proof. all: decide equality; auto with eq_dec_db. Defined.

Hint Resolve val_eq_dec : eq_dec_db.
Hint Resolve fun_clo_eq_dec : eq_dec_db.
Hint Resolve fix_clo_eq_dec : eq_dec_db.
Hint Resolve kont_clo_eq_dec : eq_dec_db.
Hint Resolve try_clo_eq_dec : eq_dec_db.
Hint Resolve handle_clo_eq_dec : eq_dec_db.
Hint Resolve shallow_handle_clo_eq_dec : eq_dec_db.
Hint Resolve kont_eq_dec : eq_dec_db.
Hint Resolve metakont_eq_dec : eq_dec_db.
Hint Resolve env_eq_dec : eq_dec_db.
Hint Resolve exn_eq_dec : eq_dec_db.
Hint Resolve eff_eq_dec : eq_dec_db.
