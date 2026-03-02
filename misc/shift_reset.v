Inductive type : Type :=
| TyLift : Type -> type
| TyFun : type -> type -> type -> type -> type.

Notation "t \ a -> s \ b" := (TyFun t s a b) (at level 40).
Notation "` t" := (TyLift t) (at level 30).

Section Syntax.
  Variable var : type -> Type.

  Inductive expr : type -> type -> type -> Type :=
  | Var : forall (t a : type), var t -> expr t a a
  | Const : forall (t : Type) (a : type), t -> expr (TyLift t) a a
  | Fun : forall (dom ran a b c : type), (var dom -> expr ran a b) -> expr (TyFun dom ran a b) c c
  | App : forall (dom ran a b c d : type), expr (TyFun dom ran a b) c d -> expr dom b c -> expr ran a d
  | Lift : forall (s t : Type) (a b : type), (s -> t) -> expr (TyLift s) a b -> expr (TyLift t) a b
  | Lift2 : forall (r s t : Type) (a b c : type), (r -> s -> t) -> expr (TyLift r) b c -> expr (TyLift s) a b -> expr (TyLift t) a c
  | Let : forall (s t a b c : type), expr s b c -> (var s -> expr t a b) -> expr t a c
  | Seq : forall (s t a b c : type), expr s b c -> expr t a b -> expr t a c
  | If : forall (t a b c : type), expr (TyLift bool) b c -> expr t a b -> expr t a b -> expr t a c
  | Shift : forall (t a b c : type), ((forall (d : type), var (TyFun t a d d)) -> expr c c b) -> expr t a b
  | Reset : forall (t a b : type), expr a a t -> expr t b b.
End Syntax.

Fixpoint type_denote (t : type) : Type :=
  match t with
  | TyLift t => t
  | TyFun dom ran a b => type_denote dom -> (type_denote ran -> type_denote a) -> type_denote b
  end.

Lemma fold_unfold_type_denote_TyLift :
  forall (t : Type),
    type_denote (TyLift t) = t.
Proof. auto. Qed.

Lemma fold_unfold_type_denote_TyFun :
  forall (dom ran a b : type),
    type_denote (TyFun dom ran a b) =
    (type_denote dom -> (type_denote ran -> type_denote a) -> type_denote b).
Proof. auto. Qed.

(** [x : Expr t a b] means that the term [x] has type [t] and evaluation of it changes the answer type from [a] to [b]. *)
Definition Expr t a b := forall var, expr var t a b.

Fixpoint interpret_aux (t a b : type) (e : expr type_denote t a b) (k : type_denote t -> type_denote a) : type_denote b.
Proof.
  inversion e as
    [ t' a' x Eq_t Eq_a Eq_b
    | t' a' v Eq_t Eq_a Eq_b
    | dom ran a' b' c f Eq_t Eq_a Eq_b
    | dom ran a' b' c d e1 e2 Eq_t Eq_a Eq_b
    | s t' a' b' f e' Eq_t Eq_a Eq_b
    | r s t' a' b' c f e1 e2 Eq_t Eq_a Eq_b
    | s t' a' b' c e' f Eq_t Eq_a Eq_b
    | s t' a' b' c e1 e2 Eq_t Eq_a Eq_b
    | t' a' b' c eb e1 e2 Eq_t Eq_a Eq_b
    | t' a' b' c f Eq_t Eq_a Eq_b
    | t' a' b' e' Eq_t Eq_a Eq_b]; clear e.
  - rewrite <- Eq_b.
    exact (k x).
  - rewrite <- Eq_t in k.
    rewrite <- Eq_b.
    exact (k v).
  - rewrite <- Eq_t in k.
    rewrite <- Eq_b.
    exact (k (fun x => interpret_aux ran a' b' (f x))).
  - exact (interpret_aux (TyFun dom t a b') c b e1 (fun f => interpret_aux dom b' c e2 (fun x => f x k))).
  - rewrite <- Eq_t in k.
    exact (interpret_aux (TyLift s) a b e' (fun x => k (f x))).
  - rewrite <- Eq_t in k.
    exact (interpret_aux (TyLift r) b' b e1 (fun x => interpret_aux (TyLift s) a b' e2 (fun y => k (f x y)))).
  - exact (interpret_aux s b' b e' (fun x => interpret_aux t a b' (f x) k)).
  - exact (interpret_aux s b' b e1 (fun _ => interpret_aux t a b' e2 k)).
  - exact (interpret_aux (TyLift bool) b' b eb (fun x => interpret_aux t a b' (if x then e1 else e2) k)).
  - exact (interpret_aux c c b (f (fun _ x k' => k' (k x))) (fun x => x)).
  - rewrite <- Eq_b.
    exact (k (interpret_aux a' a' t e' (fun x => x))).
Defined.

Definition interpret (t : type) (e : expr type_denote t t t) : type_denote t :=
  interpret_aux t t t e (fun x => x).

Lemma fold_unfold_interpret_aux_Var :
  forall (t a : type)
         (x : type_denote t)
         (k : type_denote t -> type_denote a),
    interpret_aux t a a (Var type_denote t a x) k =
    k x.
Proof. auto. Qed.

Lemma fold_unfold_interpret_aux_Const :
  forall (t : Type)
         (a : type)
         (v : t)
         (k : t -> type_denote a),
    interpret_aux (TyLift t) a a (Const type_denote t a v) k =
    k v.
Proof. auto. Qed.

Lemma fold_unfold_interpret_aux_Fun :
  forall (dom ran a b c : type)
         (f : type_denote dom -> expr type_denote ran a b)
         (k : (type_denote dom -> (type_denote ran -> type_denote a) -> type_denote b) -> type_denote c),
    interpret_aux (TyFun dom ran a b) c c (Fun type_denote dom ran a b c f) k =
    k (fun x => interpret_aux ran a b (f x)).
Proof. auto. Qed.

Lemma fold_unfold_interpret_aux_App :
  forall (dom ran a b c d : type)
         (e1 : expr type_denote (TyFun dom ran a b) c d)
         (e2 : expr type_denote dom b c)
         (k : type_denote ran -> type_denote a),
    interpret_aux ran a d (App type_denote dom ran a b c d e1 e2) k =
    interpret_aux (TyFun dom ran a b) c d e1 (fun f => interpret_aux dom b c e2 (fun x => f x k)).
Proof. auto. Qed.

Lemma fold_unfold_interpret_aux_Lift :
  forall (s t : Type)
         (a b : type)
         (f : s -> t)
         (e : expr type_denote (TyLift s) a b)
         (k : t -> type_denote a),
    interpret_aux (TyLift t) a b (Lift type_denote s t a b f e) k =
    interpret_aux (TyLift s) a b e (fun x => k (f x)).
Proof. auto. Qed.

Lemma fold_unfold_interpret_aux_Lift2 :
  forall (r s t : Type)
         (a b c : type)
         (f : r -> s -> t)
         (e1 : expr type_denote (TyLift r) b c)
         (e2 : expr type_denote (TyLift s) a b)
         (k : t -> type_denote a),
    interpret_aux (TyLift t) a c (Lift2 type_denote r s t a b c f e1 e2) k =
    interpret_aux (TyLift r) b c e1 (fun x => interpret_aux (TyLift s) a b e2 (fun y => k (f x y))).
Proof. auto. Qed.

Lemma fold_unfold_interpret_aux_Let :
  forall (s t a b c : type)
         (e : expr type_denote s b c)
         (f : type_denote s -> expr type_denote t a b)
         (k : type_denote t -> type_denote a),
    interpret_aux t a c (Let type_denote s t a b c e f) k =
    interpret_aux s b c e (fun x => interpret_aux t a b (f x) k).
Proof. auto. Qed.

Lemma fold_unfold_interpret_aux_Seq :
  forall (s t a b c : type)
         (e1 : expr type_denote s b c)
         (e2 : expr type_denote t a b)
         (k : type_denote t -> type_denote a),
    interpret_aux t a c (Seq type_denote s t a b c e1 e2) k =
    interpret_aux s b c e1 (fun _ => interpret_aux t a b e2 k).
Proof. auto. Qed.

Lemma fold_unfold_interpret_aux_If :
  forall (t a b c : type)
         (eb : expr type_denote (TyLift bool) b c)
         (e1 e2 : expr type_denote t a b)
         (k : type_denote t -> type_denote a),
    interpret_aux t a c (If type_denote t a b c eb e1 e2) k =
    interpret_aux (TyLift bool) b c eb (fun x => interpret_aux t a b (if x then e1 else e2) k).
Proof. auto. Qed.

Lemma fold_unfold_interpret_aux_Shift :
  forall (t a b c : type)
         (f : (forall (d : type), type_denote t -> (type_denote a -> type_denote d) -> type_denote d) -> expr type_denote c c b)
         (k : type_denote t -> type_denote a),
    interpret_aux t a b (Shift type_denote t a b c f) k =
    interpret_aux c c b (f (fun _ x k' => k' (k x))) (fun x => x).
Proof. auto. Qed.

Lemma fold_unfold_interpret_aux_Reset :
  forall (t a b : type)
         (e : expr type_denote a a t)
         (k : type_denote t -> type_denote b),
    interpret_aux t b b (Reset type_denote t a b e) k =
    k (interpret_aux a a t e (fun x => x)).
Proof. auto. Qed.

Require String List Arith.
Import List.ListNotations.

Open Scope list_scope.
Open Scope string_scope.

Module Lists.
  Import List.

  Lemma fold_unfold_app_nil :
    forall (A : Type)
           (ys : list A),
      [] ++ ys = ys.
  Proof. auto. Qed.

  Lemma fold_unfold_app_cons :
    forall (A : Type)
           (x : A)
           (xs' ys : list A),
      (x :: xs') ++ ys = x :: xs' ++ ys.
  Proof. auto. Qed.

  Lemma fold_unfold_rev_append_nil :
    forall (A : Type)
           (ys : list A),
      rev_append [] ys = ys.
  Proof. auto. Qed.

  Lemma fold_unfold_rev_append_cons :
    forall (A : Type)
           (x : A)
           (xs' ys : list A),
      rev_append (x :: xs') ys = rev_append xs' (x :: ys).
  Proof. auto. Qed.
End Lists.


Module AppendExample.
  Import List Arith Lists.

  Fixpoint append_delim_aux (A : Type) (xs : list A) :
    expr type_denote
      (TyLift (list A))
      (TyLift (list A))
      (TyFun (TyLift (list A)) (TyLift (list A)) (TyLift (list A)) (TyLift (list A))) :=
    match xs with
    | [] => Shift _ _ _ _ _ (fun k => Var _ _ _ (k _))
    | x :: xs' => Lift _ _ _ _ _ (cons x) (append_delim_aux A xs')
    end.

  Lemma fold_unfold_append_delim_aux_nil :
    forall (A : Type),
      append_delim_aux A [] =
      Shift _ _ _ _ _ (fun k => Var _ _ _ (k _)).
  Proof. auto. Qed.

  Lemma fold_unfold_append_delim_aux_cons :
    forall (A : Type)
           (x : A)
           (xs' : list A),
      append_delim_aux A (x :: xs') =
      Lift _ _ _ _ _ (cons x) (append_delim_aux A xs').
  Proof. auto. Qed.

  Definition append_delim (A : Type) (xs ys : list A) :
    expr type_denote
      (TyLift (list A))
      (TyLift (list A))
      (TyLift (list A)) :=
    App _ _ _ _ _ _ _ (Reset _ _ _ _ (append_delim_aux A xs)) (Const _ _ _ ys).

  Definition append_delim_unit_tests : bool :=
    let unit_test xs ys := if list_eq_dec Nat.eq_dec (interpret _ (append_delim nat xs ys)) (xs ++ ys) then true else false in
    unit_test [] []
    && unit_test [] [0]
    && unit_test [0] []
    && unit_test [0; 1] []
    && unit_test [] [0; 1]
    && unit_test [0] [1]
    && unit_test [0; 1] [2]
    && unit_test [0] [1; 2]
    && unit_test [0; 1] [2; 3].

  Compute append_delim_unit_tests.

  Lemma append_delim_is_equivalence_to_append_aux :
    forall (A : Type)
           (xs ys : list A)
           (k : list A -> list A),
      interpret_aux
        (TyLift (list A))
        (TyLift (list A))
        (TyFun (TyLift (list A)) (TyLift (list A)) (TyLift (list A)) (TyLift (list A)))
        (append_delim_aux A xs) k ys (fun x => x) =
      k (xs ++ ys).
  Proof.
    intros A xs ys.
    induction xs as [| x xs' IHxs']; intros k.
    - rewrite -> fold_unfold_append_delim_aux_nil.
      rewrite -> fold_unfold_interpret_aux_Shift.
      rewrite -> fold_unfold_interpret_aux_Var.
      rewrite -> fold_unfold_app_nil.
      reflexivity.
    - rewrite -> fold_unfold_append_delim_aux_cons.
      rewrite -> fold_unfold_interpret_aux_Lift.
      rewrite -> fold_unfold_app_cons.
      rewrite -> (IHxs' (fun r : type_denote (TyLift (list A)) => k (x :: r))).
      reflexivity.
  Qed.

  Theorem append_delim_is_equivalence_to_append :
    forall (A : Type)
           (xs ys : list A),
      interpret (TyLift (list A)) (append_delim A xs ys) =
      xs ++ ys.
  Proof.
    intros A xs ys.
    unfold interpret, append_delim.
    rewrite -> fold_unfold_interpret_aux_App.
    rewrite -> fold_unfold_interpret_aux_Reset.
    rewrite -> fold_unfold_interpret_aux_Const.
    exact (append_delim_is_equivalence_to_append_aux A xs ys (fun x => x)).
  Qed.
End AppendExample.


Module TimesExample.
  Import Arith.

  Fixpoint times_delim_aux (xs : list nat) :
    expr type_denote
      (TyLift nat)
      (TyLift nat)
      (TyLift nat) :=
    match xs with
    | [] => Const _ _ _ 1
    | x :: xs' => match x with
                  | O => Shift _ _ _ _ _ (fun _ => Const _ _ _ 0)
                  | _ => Lift _ _ _ _ _ (Nat.mul x) (times_delim_aux xs')
                  end
    end.

  Definition times_delim (xs : list nat) :
    expr type_denote
      (TyLift nat)
      (TyLift nat)
      (TyLift nat) :=
    Reset _ _ _ _ (times_delim_aux xs).

  Lemma fold_unfold_times_delim_aux_nil :
    times_delim_aux [] =
    Const _ _ _ 1.
  Proof. auto. Qed.

  Lemma fold_unfold_times_delim_aux_cons :
    forall (x : nat)
           (xs' : list nat),
      times_delim_aux (x :: xs') =
      match x with
      | O => Shift _ _ _ _ _ (fun _ => Const _ _ _ 0)
      | _ => Lift _ _ _ _ _ (Nat.mul x) (times_delim_aux xs')
      end.
  Proof. auto. Qed.

  Fixpoint times (xs : list nat) : nat :=
    match xs with
    | [] => 1
    | x :: xs' => x * times xs'
    end.

  Lemma fold_unfold_times_nil :
    times [] = 1.
  Proof. auto. Qed.

  Lemma fold_unfold_times_cons :
    forall (x : nat)
           (xs' : list nat),
      times (x :: xs') = x * times xs'.
  Proof. auto. Qed.

  Lemma times_delim_is_equivalence_to_times_aux :
    forall (xs : list nat)
           (k : nat -> nat),
      interpret_aux (TyLift nat) (TyLift nat) (TyLift nat) (times_delim_aux xs) k =
      match times xs with
      | O => O
      | S r' => k (S r')
      end.
  Proof.
    intros xs.
    induction xs as [| x xs' IHxs']; intros k.
    - rewrite -> fold_unfold_times_delim_aux_nil.
      rewrite -> fold_unfold_interpret_aux_Const.
      rewrite -> fold_unfold_times_nil.
      reflexivity.
    - rewrite -> fold_unfold_times_delim_aux_cons.
      rewrite -> fold_unfold_times_cons.
      destruct x as [| x'].
      + rewrite -> fold_unfold_interpret_aux_Shift.
        rewrite -> fold_unfold_interpret_aux_Const.
        reflexivity.
      + rewrite -> fold_unfold_interpret_aux_Lift.
        rewrite -> (IHxs' (fun r : type_denote (TyLift nat) => k (S x' * r))).
        destruct (times xs') as [| r'].
        * rewrite -> Nat.mul_0_r.
          reflexivity.
        * reflexivity.
  Qed.

  Theorem times_delim_is_equivalence_to_times :
    forall (xs : list nat),
      interpret (TyLift nat) (times_delim xs) =
      times xs.
  Proof.
    intros xs.
    unfold interpret, times_delim.
    rewrite -> fold_unfold_interpret_aux_Reset.
    assert (ly := times_delim_is_equivalence_to_times_aux xs (fun x => x)).
    destruct (times xs) as [| r'].
    - exact ly.
    - exact ly.
  Qed.
End TimesExample.


Module MulPow2Example.
  Import Arith.

  Definition either (A B : Type) (x y : A) (f : B -> B -> B) : expr type_denote (TyLift A) (TyLift B) (TyLift B) :=
    Shift _ _ _ _ _ (fun k => Lift2 _ _ _ _ _ _ _ f
                                (App _ _ _ _ _ _ _ (Var _ _ _ (k _)) (Const _ _ _ x))
                                (App _ _ _ _ _ _ _ (Var _ _ _ (k _)) (Const _ _ _ y))).

  Fixpoint mul_pow2_delim_aux (n : nat) : expr type_denote (TyLift unit) (TyLift nat) (TyLift nat) :=
    match n with
    | O => Const _ _ _ tt
    | S n' => Seq _ _ _ _ _ _ (either unit nat tt tt Nat.add) (mul_pow2_delim_aux n')
    end.

  Definition mul_pow2_delim (m n : nat) : expr type_denote (TyLift nat) (TyLift nat) (TyLift nat) :=
    Reset _ _ _ _ (Lift _ _ _ _ _ (fun _ => m) (mul_pow2_delim_aux n)).

  Lemma fold_unfold_mul_pow2_delim_aux_O :
    mul_pow2_delim_aux O =
    Const _ _ _ tt.
  Proof. auto. Qed.

  Lemma fold_unfold_mul_pow2_delim_aux_S :
    forall (n' : nat),
      mul_pow2_delim_aux (S n') =
      Seq _ _ _ _ _ _ (either unit nat tt tt Nat.add) (mul_pow2_delim_aux n').
  Proof. auto. Qed.

  Lemma mul_pow2_delim_is_sound_aux :
    forall (m n : nat),
      interpret_aux (TyLift unit) (TyLift nat) (TyLift nat) (mul_pow2_delim_aux n) (fun _ => m) =
      m * 2 ^ n.
  Proof.
    intros m n.
    induction n as [| n' IHn'].
    - rewrite -> fold_unfold_mul_pow2_delim_aux_O.
      rewrite -> fold_unfold_interpret_aux_Const.
      cbn. ring.
    - rewrite -> fold_unfold_mul_pow2_delim_aux_S.
      rewrite -> fold_unfold_interpret_aux_Seq.
      unfold either.
      rewrite -> fold_unfold_interpret_aux_Shift.
      rewrite -> fold_unfold_interpret_aux_Lift2.
      rewrite -> fold_unfold_interpret_aux_App.
      rewrite -> fold_unfold_interpret_aux_Var.
      rewrite -> fold_unfold_interpret_aux_Const.
      rewrite -> fold_unfold_interpret_aux_App.
      rewrite -> fold_unfold_interpret_aux_Var.
      rewrite -> fold_unfold_interpret_aux_Const.
      rewrite -> IHn'.
      cbn. ring.
  Qed.

  Theorem mul_pow2_delim_is_sound :
    forall (m n : nat),
      interpret (TyLift nat) (mul_pow2_delim m n) =
      m * 2 ^ n.
  Proof.
    intros m n.
    unfold interpret, mul_pow2_delim.
    rewrite -> fold_unfold_interpret_aux_Reset.
    rewrite -> fold_unfold_interpret_aux_Lift.
    exact (mul_pow2_delim_is_sound_aux m n).
  Qed.
End MulPow2Example.


Theorem interpret_aux_Let_assoc :
  forall (r s t a b c d : type)
         (e : expr type_denote r c d)
         (f : type_denote r -> expr type_denote s b c)
         (g : type_denote s -> expr type_denote t a b)
         (k : type_denote t -> type_denote a),
    interpret_aux _ _ _ (Let _ _ _ _ _ _ (Let _ _ _ _ _ _ e f) g) k =
    interpret_aux _ _ _ (Let _ _ _ _ _ _ e (fun x => Let _ _ _ _ _ _ (f x) g)) k.
Proof.
  intros r s t a b c d e f g k.
  (* Using only fold-unfold lemma will not work here, as we
     cannot rewrite under a binder. But reduction (cbn) still
     works under a binder, and thus we can still prove this. *)
  cbn. reflexivity.
Qed.

(* An example which illustrates that continuation may take
   an ATM function as argument. *)
Example e0 :=
  (fun var dom ran c =>
     Shift _ _ _ _ _
       (fun k =>
          App _ _ _ _ _ _ _
            (Var _ _ _ (k _))
            (Fun _ _ _ _ _ _
               (fun _ =>
                  Shift _ _ _ _ _
                    (fun _ => Const _ _ _ 1)))) :
     expr var (TyFun dom ran (TyLift unit) (TyLift nat)) c c).

Example e1 :=
  (fun var dom ran c =>
     Reset _ _ _ _ (e0 _ _ _ _) :
     expr var (TyFun dom ran (TyLift unit) (TyLift nat)) c c).

Example e2 :=
  (fun var ran =>
     App _ _ _ _ _ _ _ (e1 _ _ _ _) (Const _ _ _ tt) :
     expr var ran (TyLift unit) (TyLift nat)).

Example e3 :=
  (fun var c =>
     Reset _ _ _ _ (e2 _ _) :
     expr var (TyLift nat) c c).

Goal interpret _ (e3 _ _) = 1.
Proof.
  unfold interpret.
  unfold e3, e2, e1, e0.
  rewrite -> fold_unfold_interpret_aux_Reset.
  rewrite -> fold_unfold_interpret_aux_App.
  rewrite -> fold_unfold_interpret_aux_Reset.
  rewrite -> fold_unfold_interpret_aux_Shift.
  rewrite -> fold_unfold_interpret_aux_App.
  rewrite -> fold_unfold_interpret_aux_Var.
  rewrite -> fold_unfold_interpret_aux_Const.
  rewrite -> fold_unfold_interpret_aux_Fun.
  rewrite -> fold_unfold_interpret_aux_Shift.
  rewrite -> fold_unfold_interpret_aux_Const.
  reflexivity.
Qed.


Module CopyExample.
  Parameter copy_delim_aux :
    forall (A : Type),
      list A ->
      expr type_denote (TyLift (list A)) (TyLift (list A)) (TyLift (list A)).

  Axiom fold_unfold_copy_delim_aux_nil :
    forall (A : Type),
      copy_delim_aux A [] =
      Const _ _ _ [].

  Axiom fold_unfold_copy_delim_aux_cons :
    forall (A : Type)
           (x : A)
           (xs' : list A),
      copy_delim_aux A (x :: xs') =
      Let _ _ _ _ _ _
        (Shift _ _ _ _ _ (fun k => Lift _ _ _ _ _ (cons x) (App _ _ _ _ _ _ _ (Var _ _ _ (k _)) (Const _ _ _ xs'))))
        (copy_delim_aux A).

  Definition copy_delim (A : Type) (xs : list A) (c : type) : expr type_denote (TyLift (list A)) c c :=
    Reset _ _ _ _ (copy_delim_aux A xs).

  Lemma copy_delim_is_sound_aux :
    forall (A : Type)
           (xs : list A),
      interpret_aux (TyLift (list A)) (TyLift (list A)) (TyLift (list A)) (copy_delim_aux A xs) (fun x => x) =
      xs.
  Proof.
    intros A xs.
    induction xs as [| x xs' IHxs'].
    - rewrite -> fold_unfold_copy_delim_aux_nil.
      rewrite -> fold_unfold_interpret_aux_Const.
      reflexivity.
    - rewrite -> fold_unfold_copy_delim_aux_cons.
      rewrite -> fold_unfold_interpret_aux_Let.
      rewrite -> fold_unfold_interpret_aux_Shift.
      rewrite -> fold_unfold_interpret_aux_Lift.
      rewrite -> fold_unfold_interpret_aux_App.
      rewrite -> fold_unfold_interpret_aux_Var.
      rewrite -> fold_unfold_interpret_aux_Const.
      rewrite -> IHxs'.
      reflexivity.
  Qed.

  Theorem copy_delim_is_sound :
    forall (A : Type)
           (xs : list A),
      interpret (TyLift (list A)) (copy_delim A xs (TyLift (list A))) =
      xs.
  Proof.
    intros A xs.
    unfold interpret, copy_delim.
    rewrite -> fold_unfold_interpret_aux_Reset.
    exact (copy_delim_is_sound_aux A xs).
  Qed.

End CopyExample.


Module PrefixesExample.
  Import List Arith Lists.

  Fixpoint prefixes_delim_aux (A : Type) (xs : list A) :
    expr type_denote
      (TyLift (list A))
      (TyLift (list A))
      (TyLift (list (list A))) :=
    Shift _ _ _ _ _
      (fun k => Lift2 _ _ _ _ _ _ _ cons
                  (App _ _ _ _ _ _ _ (Var _ _ _ (k _)) (Const _ _ _ []))
                  match xs with
                  | [] => Const _ _ _ []
                  | x :: xs' => Reset _ _ _ _ (App _ _ _ _ _ _ _ (Var _ _ _ (k _)) (Lift _ _ _ _ _ (cons x) (prefixes_delim_aux A xs')))
                  end).

  Definition prefixes_delim (A : Type) (xs : list A) :
    expr type_denote
      (TyLift (list (list A)))
      (TyLift (list (list A)))
      (TyLift (list (list A))) :=
    Reset _ _ _ _ (prefixes_delim_aux A xs).

  Lemma fold_unfold_prefixes_delim_aux_nil :
    forall (A : Type),
      prefixes_delim_aux A [] =
      Shift _ _ _ _ _
        (fun k => Lift2 _ _ _ _ _ _ _ cons
                    (App _ _ _ _ _ _ _ (Var _ _ _ (k _)) (Const _ _ _ []))
                    (Const _ _ _ [])).
  Proof. auto. Qed.

  Lemma fold_unfold_prefixes_delim_aux_cons :
    forall (A : Type)
           (x : A)
           (xs' : list A),
      prefixes_delim_aux A (x :: xs') =
      Shift _ _ _ _ _
        (fun k => Lift2 _ _ _ _ _ _ _ cons
                    (App _ _ _ _ _ _ _ (Var _ _ _ (k _)) (Const _ _ _ []))
                    (Reset _ _ _ _ (App _ _ _ _ _ _ _ (Var _ _ _ (k _)) (Lift _ _ _ _ _ (cons x) (prefixes_delim_aux A xs'))))).
  Proof. auto. Qed.

  Fixpoint fo_prefixes_aux (A : Type) (xs acc : list A) : list (list A) :=
    rev_append acc [] ::
      match xs with
      | [] => []
      | x :: xs' => fo_prefixes_aux A xs' (x :: acc)
      end.

  Definition fo_prefixes (A : Type) (xs : list A) : list (list A) :=
    fo_prefixes_aux A xs [].

  Lemma fold_unfold_fo_prefixes_aux_nil :
    forall (A : Type)
           (acc : list A),
      fo_prefixes_aux A [] acc =
      [rev_append acc []].
  Proof. auto. Qed.

  Lemma fold_unfold_fo_prefixes_aux_cons :
    forall (A : Type)
           (x : A)
           (xs' acc : list A),
      fo_prefixes_aux A (x :: xs') acc =
      rev_append acc [] :: fo_prefixes_aux A xs' (x :: acc).
  Proof. auto. Qed.

  Definition prefixes_delim_unit_tests : bool :=
    let unit_test xs :=
      if list_eq_dec
           (list_eq_dec Nat.eq_dec)
           (interpret _ (prefixes_delim nat xs))
           (fo_prefixes nat xs)
      then true
      else false
    in
    unit_test []
    && unit_test [0]
    && unit_test [0; 1]
    && unit_test [0; 1; 2]
    && unit_test [0; 1; 2; 3]
    && unit_test [0; 1; 2; 3; 4]
    && unit_test [0; 1; 2; 3; 4; 5].

  Compute prefixes_delim_unit_tests.

  Lemma prefixes_delim_is_equivalent_to_fo_prefixes_aux :
    forall (A : Type)
           (xs : list A)
           (k : list A -> list A)
           (acc : list A),
      (forall (ys : list A), k ys = rev_append acc ys) ->
      interpret_aux (TyLift (list A)) (TyLift (list A)) (TyLift (list (list A))) (prefixes_delim_aux A xs) k =
      fo_prefixes_aux A xs acc.
  Proof.
    intros A xs.
    induction xs as [| x xs' IHxs']; intros k acc H_eq.
    - rewrite -> fold_unfold_prefixes_delim_aux_nil.
      rewrite -> fold_unfold_interpret_aux_Shift.
      rewrite -> fold_unfold_interpret_aux_Lift2.
      rewrite -> fold_unfold_interpret_aux_App.
      rewrite -> fold_unfold_interpret_aux_Var.
      rewrite -> fold_unfold_interpret_aux_Const.
      rewrite -> fold_unfold_interpret_aux_Const.
      rewrite -> fold_unfold_fo_prefixes_aux_nil.
      rewrite -> (H_eq []).
      reflexivity.
    - rewrite -> fold_unfold_prefixes_delim_aux_cons.
      rewrite -> fold_unfold_interpret_aux_Shift.
      rewrite -> fold_unfold_interpret_aux_Lift2.
      rewrite -> fold_unfold_interpret_aux_App.
      rewrite -> fold_unfold_interpret_aux_Var.
      rewrite -> fold_unfold_interpret_aux_Const.
      rewrite -> fold_unfold_interpret_aux_Reset.
      rewrite -> fold_unfold_interpret_aux_App.
      rewrite -> fold_unfold_interpret_aux_Var.
      rewrite -> fold_unfold_interpret_aux_Lift.
      rewrite -> fold_unfold_fo_prefixes_aux_cons.
      rewrite -> (H_eq []).
      assert (H_eq' : forall (ys : list A), k (x :: ys) = rev_append (x :: acc) ys).
      { intros ys.
        rewrite -> (H_eq (x :: ys)).
        rewrite -> fold_unfold_rev_append_cons.
        reflexivity. }
      rewrite -> (IHxs' (fun r : type_denote (TyLift (list A)) => k (x :: r)) (x :: acc) H_eq').
      reflexivity.
  Qed.

  Theorem prefixes_delim_is_equivalent_to_fo_prefixes :
    forall (A : Type)
           (xs : list A),
      interpret (TyLift (list (list A))) (prefixes_delim A xs) =
      fo_prefixes A xs.
  Proof.
    intros A xs.
    unfold interpret, prefixes_delim, fo_prefixes.
    rewrite -> fold_unfold_interpret_aux_Reset.
    assert (H_eq : forall (ys : list A), ys = rev_append [] ys).
    { intros ys.
      rewrite -> fold_unfold_rev_append_nil.
      reflexivity. }
    exact (prefixes_delim_is_equivalent_to_fo_prefixes_aux A xs (fun x => x) [] H_eq).
  Qed.
End PrefixesExample.


Module PrintfExample.
  Import String.

  Definition TyString : type := TyLift string.
  Definition TyNat : type := TyLift nat.

  Definition of_string (s : string) : string := s.
  Definition of_nat (n : nat) : string := "10".

  Definition get (a : type) (A : Type) (to_string : A -> string) :
    expr type_denote TyString a (TyFun (TyLift A) a TyString TyString) :=
    Shift _ _ _ _ _ (fun k => Fun _ _ _ _ _ _ (fun x => App _ _ _ _ _ _ _ (Var _ _ _ (k _)) (Lift _ _ _ _ _ to_string (Var _ _ _ x)))).

  Example ex_fmt1 :
    expr type_denote TyString TyString TyString :=
    Const _ _ _ "Hello world!".

  Example ex_fmt2 :
    expr type_denote
      TyString
      TyString
      (TyFun TyString TyString TyString TyString) :=
    Lift2 _ _ _ _ _ _ _ append (Const _ _ _ "Hello ") (Lift2 _ _ _ _ _ _ _ append (get _ _ of_string) (Const _ _ _ "!")).

  Example ex_fmt3 :
    expr type_denote
      TyString
      TyString
      (TyFun
         TyString
         (TyFun TyNat TyString TyString TyString)
         TyString
         TyString) :=
    Lift2 _ _ _ _ _ _ _ append
      (Const _ _ _ "The value of ")
      (Lift2 _ _ _ _ _ _ _ append (get _ _ of_string) (Lift2 _ _ _ _ _ _ _ append (Const _ _ _ " is ") (get _ _ of_nat))).

  Definition sprintf (a : type) (fmt : expr type_denote TyString TyString a) :
    expr type_denote a TyString TyString :=
    Reset _ _ _ _ fmt.

  Compute (interpret _ (sprintf _ ex_fmt1)).
  Compute (interpret _ (App _ _ _ _ _ _ _ (sprintf _ ex_fmt2) (Const _ _ _ "world"))).
  Compute (interpret _ (App _ _ _ _ _ _ _ (App _ _ _ _ _ _ _ (sprintf _ ex_fmt3) (Const _ _ _ "x")) (Const _ _ _ 10))).
End PrintfExample.
