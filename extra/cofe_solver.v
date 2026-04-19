From Stdlib Require Import FunctionalExtensionality Arith Morphisms.

Parameter dist : forall {A}, nat -> A -> A -> Prop.
Notation "x ={ n }= y" := (dist n x y) (at level 70).

Axiom dist_refl : forall {A} (n : nat) (x : A), x ={n}= x.
Axiom dist_sym : forall {A} (n : nat) (x y : A), x ={n}= y -> y ={n}= x.
Axiom dist_trans : forall {A} (n : nat) (x y z : A), x ={n}= y -> y ={n}= z -> x ={n}= z.
Axiom dist_le : forall {A} (n m : nat) (x y : A), m <= n -> x ={n}= y -> x ={m}= y.

Instance dist_Reflexive {A} (n : nat) : Reflexive (@dist A n).
Proof. exact (dist_refl n). Qed.

Instance dist_Symmetric {A} (n : nat) : Symmetric (@dist A n).
Proof. exact (dist_sym n). Qed.

Instance dist_Transitive {A} (n : nat) : Transitive (@dist A n).
Proof. exact (dist_trans n). Qed.

Instance dist_Equivalence {A} (n : nat) : Equivalence (@dist A n).
Proof. constructor. apply dist_Reflexive. apply dist_Symmetric. apply dist_Transitive. Qed.

Instance dist_RewriteRelation {A} (n : nat) : RewriteRelation (@dist A n) := {}.

Axiom eq_dist : forall {A} (x y : A), x = y <-> forall n, x ={n}= y.
Axiom dist_ext : forall {A B} (n : nat) (f g : A -> B), f ={n}= g <-> forall x, f x ={n}= g x.
Axiom dist_ext_dep : forall {A} {B : A -> Type} (n : nat) (f g : forall x, B x), f ={n}= g <-> forall x, f x ={n}= g x.

Class NonExpansive {A B} (f : A -> B) : Prop :=
  f_ne (n : nat) (x y : A) : x ={n}= y -> f x ={n}= f y.

Class NonExpansive2 {A B C} (f : A -> B -> C) : Prop :=
  f_ne2 (n : nat) (x y : A) (u v : B) : x ={n}= y -> u ={n}= v -> f x u ={n}= f y v.

Class NonExpansive3 {A B C D} (f : A -> B -> C -> D) : Prop :=
  f_ne3 (n : nat) (x y : A) (u v : B) (s t : C) : x ={n}= y -> u ={n}= v -> s ={n}= t -> f x u s ={n}= f y v t.

Lemma ne_dist {A B} (f : A -> B) {H_ne : NonExpansive f} :
  forall (n : nat) (x y : A), x ={n}= y -> f x ={n}= f y.
Proof. exact f_ne. Qed.

Lemma ne2_dist {A B C} (f : A -> B -> C) {H_ne2 : NonExpansive2 f} :
  forall (n : nat) (x y : A) (u v : B), x ={n}= y -> u ={n}= v -> f x u ={n}= f y v.
Proof. exact f_ne2. Qed.

Lemma ne3_dist {A B C D} (f : A -> B -> C -> D) {H_ne3 : NonExpansive3 f} :
  forall (n : nat) (x y : A) (u v : B) (s t : C), x ={n}= y -> u ={n}= v -> s ={n}= t -> f x u s ={n}= f y v t.
Proof. exact f_ne3. Qed.

Class Contractive {A B} (f : A -> B) : Prop :=
  f_contractive : forall (n : nat) (x y : A), (forall m, m < n -> x ={m}= y) -> f x ={n}= f y.

Lemma contractive_dist {A B} (f : A -> B) {H_contractive : Contractive f} :
  forall (n : nat) (x y : A), (forall m, m < n -> x ={m}= y) -> f x ={n}= f y.
Proof. exact f_contractive. Qed.

Lemma contractive_dist_O {A B} {f : A -> B} {H_contractive : Contractive f}
  (x y : A) : f x ={O}= f y.
Proof.
  apply f_contractive.
  intros m H_lt. contradict (Nat.nlt_0_r m H_lt).
Qed.

Lemma contractive_dist_S {A B} {f : A -> B} {H_contractive : Contractive f}
  (n : nat) (x y : A) (H_dist : x ={n}= y) : f x ={S n}= f y.
Proof.
  apply f_contractive.
  intros m H_lt. exact (dist_le n m x y (proj1 (Nat.lt_succ_r m n) H_lt) H_dist).
Qed.

Class Contractive2 {A B C} (f : A -> B -> C) : Prop :=
  f_contractive2 :
    forall (n : nat)
           (x y : A)
           (u v : B),
      (forall m, m < n -> x ={m}= y) ->
      (forall m, m < n -> u ={m}= v) ->
      f x u ={n}= f y v.

Lemma contractive2_dist {A B C} (f : A -> B -> C) {H_contractive2 : Contractive2 f} :
  forall (n : nat)
         (x y : A)
         (u v : B),
    (forall m, m < n -> x ={m}= y) ->
    (forall m, m < n -> u ={m}= v) ->
    f x u ={n}= f y v.
Proof. exact f_contractive2. Qed.

Lemma contractive2_dist_O {A B C} {f : A -> B -> C} {H_contractive2 : Contractive2 f}
  (x y : A) (u v : B) : f x u ={O}= f y v.
Proof.
  apply f_contractive2.
  - intros m H_lt. contradict (Nat.nlt_0_r m H_lt).
  - intros m H_lt. contradict (Nat.nlt_0_r m H_lt).
Qed.

Lemma contractive2_dist_S {A B C} {f : A -> B -> C} {H_contractive2 : Contractive2 f}
  (n : nat) (x y : A) (u v : B) (H_dist1 : x ={n}= y) (H_dist2 : u ={n}= v) : f x u ={S n}= f y v.
Proof.
  apply f_contractive2.
  - intros m H_lt. exact (dist_le n m x y (proj1 (Nat.lt_succ_r m n) H_lt) H_dist1).
  - intros m H_lt. exact (dist_le n m u v (proj1 (Nat.lt_succ_r m n) H_lt) H_dist2).
Qed.

Instance NonExpansive_Proper {A B} (f : A -> B) {H_ne : NonExpansive f} (n : nat) :
  Proper (dist n ==> dist n) f.
Proof.
  unfold Proper, respectful.
  exact (ne_dist f n).
Qed.

Instance NonExpansive2_Proper {A B C} (f : A -> B -> C) {H_ne2 : NonExpansive2 f} (n : nat) :
  Proper (dist n ==> dist n ==> dist n) f.
Proof.
  unfold Proper, respectful.
  intros x y H_dist1 u v. exact (ne2_dist f n x y u v H_dist1).
Qed.

Instance NonExpansive3_Proper {A B C D} (f : A -> B -> C -> D) {H_ne3 : NonExpansive3 f} (n : nat) :
  Proper (dist n ==> dist n ==> dist n ==> dist n) f.
Proof.
  unfold Proper, respectful.
  intros x y H_dist1 u v H_dist2 s t. exact (ne3_dist f n x y u v s t H_dist1 H_dist2).
Qed.

Lemma dist_ext2 {A B C} (n : nat) (f g : A -> B -> C) :
  f ={n}= g <-> forall x y, f x y ={n}= g x y.
Proof.
  split.
  - intros H_dist x.
    exact (proj1 (dist_ext n (f x) (g x)) (proj1 (dist_ext n f g) H_dist x)).
  - intros H_dist.
    apply (proj2 (dist_ext n f g)). intros x.
    exact (proj2 (dist_ext n (f x) (g x)) (H_dist x)).
Qed.

(* F is a profunctor *)
Parameter F : Type -> Type -> Type.
Parameter inhabitant : F unit unit.

Parameter dimap : forall {A1 A2 B1 B2}, (A2 -> A1) -> (B1 -> B2) -> F A1 B1 -> F A2 B2.
Axiom dimap_id : forall {A B} (m : F A B), dimap (fun x => x) (fun x => x) m = m.
Axiom dimap_comp :
  forall {A1 A2 A3 B1 B2 B3}
         (f : A3 -> A2)
         (g : A2 -> A1)
         (h : B1 -> B2)
         (k : B2 -> B3)
         (m : F A1 B1),
    dimap f k (dimap g h m) = dimap (fun x => g (f x)) (fun x => k (h x)) m.

Axiom dimap_NonExpansive2 : forall {A1 A2 B1 B2}, NonExpansive2 (@dimap A1 A2 B1 B2).
Axiom dimap_NonExpansive3 : forall {A1 A2 B1 B2}, NonExpansive3 (@dimap A1 A2 B1 B2).
Axiom dimap_Contractive2 : forall {A1 A2 B1 B2}, Contractive2 (@dimap A1 A2 B1 B2).
Existing Instance dimap_NonExpansive2.
Existing Instance dimap_NonExpansive3.
Existing Instance dimap_Contractive2.

Fixpoint approx (n : nat) : Type :=
  match n with
  | O => unit
  | S n' => let A := approx n' in F A A
  end.

Fixpoint up (k : nat) : approx k -> approx (S k) :=
  match k with
  | O => fun _ => inhabitant
  | S k' => dimap (down k') (up k')
  end
with down (k : nat) : approx (S k) -> approx k :=
  match k with
  | O => fun _ => tt
  | S k' => dimap (up k') (down k')
  end.

Lemma up_O (x : approx O) : up O x = inhabitant.
Proof. reflexivity. Qed.

Lemma up_S (k' : nat) (x : approx (S k')) : up (S k') x = dimap (down k') (up k') x.
Proof. reflexivity. Qed.

Lemma down_O (x : approx 1) : down O x = tt.
Proof. reflexivity. Qed.

Lemma down_S (k' : nat) (x : approx (S (S k'))) : down (S k') x = dimap (up k') (down k') x.
Proof. reflexivity. Qed.

Instance up_NonExpansive (k : nat) : NonExpansive (up k).
Proof.
  unfold NonExpansive.
  intros n x y H_dist.
  destruct k as [| k']; simpl.
  - reflexivity.
  - rewrite -> H_dist.
    reflexivity.
Qed.

Instance down_NonExpansive (k : nat) : NonExpansive (down k).
Proof.
  unfold NonExpansive.
  intros n x y H_dist.
  destruct k as [| k']; simpl.
  - reflexivity.
  - rewrite -> H_dist.
    reflexivity.
Qed.

Lemma down_up (k : nat) : forall (x : approx k), down k (up k x) = x.
Proof.
  induction k as [| k' IHk']; intros x.
  - rewrite -> down_O.
    destruct x as []. reflexivity.
  - rewrite -> down_S.
    rewrite -> up_S.
    rewrite -> dimap_comp.
    rewrite -> (functional_extensionality (fun y => down k' (up k' y)) (fun y => y) IHk').
    rewrite -> dimap_id.
    reflexivity.
Qed.

Lemma up_down (k : nat) : forall (x : approx (S (S k))), up (S k) (down (S k) x) ={k}= x.
Proof.
  induction k as [| k' IHk']; intros x.
  - rewrite -> up_S.
    rewrite -> down_S.
    rewrite -> dimap_comp.
    rewrite <- (@dimap_id (approx 1) (approx 1) x) at 2.
    apply dist_ext.
    exact (contractive2_dist_O _ _ _ _).
  - rewrite -> up_S.
    rewrite -> down_S.
    rewrite -> dimap_comp.
    rewrite <- (@dimap_id (approx (S (S k'))) (approx (S (S k'))) x) at 2.
    apply dist_ext.
    apply contractive2_dist_S.
    + exact (proj2 (dist_ext k' _ _) IHk').
    + exact (proj2 (dist_ext k' _ _) IHk').
Qed.

Fixpoint up_iter (n k : nat) (x : approx k) : approx (n + k) :=
  match n with
  | O => x
  | S n' => up (n' + k) (up_iter n' k x)
  end.

Lemma up_iter_O (k : nat) (x : approx k) : up_iter O k x = x.
Proof. reflexivity. Qed.

Lemma up_iter_S (n' k : nat) (x : approx k) :
  up_iter (S n') k x = up (n' + k) (up_iter n' k x).
Proof. reflexivity. Qed.

Fixpoint down_iter (n k : nat) : approx (n + k) -> approx k :=
  match n with
  | O => fun x => x
  | S n' => fun x => down_iter n' k (down (n' + k) x)
  end.

Lemma down_iter_O (k : nat) (x : approx k) : down_iter O k x = x.
Proof. reflexivity. Qed.

Lemma down_iter_S (n' k : nat) (x : approx (S (n' + k))) :
  down_iter (S n') k x = down_iter n' k (down (n' + k) x).
Proof. reflexivity. Qed.

Lemma down_iter_up_iter (n k : nat) (x : approx k) : down_iter n k (up_iter n k x) = x.
Proof.
  induction n as [| n' IHn']; simpl.
  - reflexivity.
  - rewrite -> down_up.
    rewrite -> IHn'.
    reflexivity.
Qed.

Definition cast (m n : nat) (H_eq : m = n) (x : approx m) : approx n :=
  let 'eq_refl := H_eq in x.

Instance cast_NonExpansive (m n : nat) (H_eq : m = n) : NonExpansive (cast m n H_eq).
Proof.
  unfold NonExpansive, cast.
  intros k x y H_dist.
  destruct H_eq as [].
  exact H_dist.
Qed.

Lemma cast_id (n : nat) (x : approx n) : cast n n eq_refl x = x.
Proof. unfold cast. reflexivity. Qed.

Lemma cast_comp (m n p : nat) (H_eq1 : m = n) (H_eq2 : n = p) (x : approx m) :
  cast n p H_eq2 (cast m n H_eq1 x) = cast m p (eq_trans H_eq1 H_eq2) x.
Proof.
  destruct H_eq1 as [].
  destruct H_eq2 as [].
  unfold cast, eq_trans. reflexivity.
Qed.

Lemma cast_natural (f g : nat -> nat) (eta : forall i, approx (f i) -> approx (g i)) (m n : nat) (H_eq : m = n) (x : approx (f m)) :
  cast (g m) (g n) (f_equal g H_eq) (eta m x) = eta n (cast (f m) (f n) (f_equal f H_eq) x).
Proof.
  destruct H_eq as [].
  unfold cast, f_equal. reflexivity.
Qed.

Lemma cast_up (m n : nat) (H_eq : m = n) (x : approx m) :
  cast (S m) (S n) (f_equal S H_eq) (up m x) = up n (cast m n H_eq x).
Proof.
  destruct H_eq as [].
  unfold cast, f_equal. reflexivity.
Qed.

Lemma down_cast (m n : nat) (H_eq : n = m) (x : approx (S n)) :
  down m (cast (S n) (S m) (f_equal S H_eq) x) = cast n m H_eq (down n x).
Proof.
  destruct H_eq as [].
  unfold cast, f_equal. reflexivity.
Qed.

Lemma cast_up_iter_r (k m n : nat) (H_eq : m = n) (x : approx m) :
  cast (k + m) (k + n) (f_equal (Nat.add k) H_eq) (up_iter k m x) = up_iter k n (cast m n H_eq x).
Proof.
  destruct H_eq as [].
  unfold cast, f_equal. reflexivity.
Qed.

Lemma down_iter_cast_r (k n m : nat) (H_eq : n = m) (x : approx (k + n)) :
  down_iter k m (cast (k + n) (k + m) (f_equal (Nat.add k) H_eq) x) = cast n m H_eq (down_iter k n x).
Proof.
  destruct H_eq as [].
  unfold cast, f_equal. reflexivity.
Qed.

Lemma cast_up_iter_l (m n k : nat) (H_eq : m = n) (x : approx k) :
  cast (m + k) (n + k) (f_equal (fun p => p + k) H_eq) (up_iter m k x) = up_iter n k x.
Proof.
  destruct H_eq as [].
  unfold cast, f_equal. reflexivity.
Qed.

Lemma down_iter_cast_l (m n k : nat) (H_eq : n = m) (x : approx (n + k)) :
  down_iter m k (cast (n + k) (m + k) (f_equal (fun p => p + k) H_eq) x) = down_iter n k x.
Proof.
  destruct H_eq as [].
  unfold cast, f_equal. reflexivity.
Qed.

Lemma cast_up_iter_up (n k : nat) (x : approx k) :
  cast (n + S k) (S (n + k)) (Nat.add_succ_r n k) (up_iter n (S k) (up k x)) =
  up_iter (S n) k x.
Proof.
  induction n as [| n' IHn'].
  - rewrite -> up_iter_S.
    rewrite -> up_iter_O.
    rewrite -> up_iter_O.
    rewrite -> (UIP_nat _ _ _ eq_refl).
    unfold cast. reflexivity.
  - rewrite -> (up_iter_S n' (S k)).
    rewrite -> (UIP_nat _ _ _ (f_equal S (Nat.add_succ_r n' k))).
    rewrite -> (cast_up (n' + S k)).
    rewrite -> IHn'.
    rewrite <- (up_iter_S (S n') k).
    reflexivity.
Qed.

Lemma down_down_iter_cast (n k : nat) :
  forall (x : approx (S (n + k))),
    down k (down_iter n (S k) (cast (S (n + k)) (n + S k) (eq_sym (Nat.add_succ_r n k)) x)) =
    down_iter (S n) k x.
Proof.
  induction n as [| n' IHn']; intros x.
  - rewrite -> down_iter_S.
    rewrite -> down_iter_O.
    rewrite -> down_iter_O.
    rewrite -> (UIP_nat _ _ _ eq_refl).
    unfold cast. reflexivity.
  - rewrite -> (down_iter_S n' (S k)).
    rewrite -> (UIP_nat _ _ _ (f_equal S (eq_sym (Nat.add_succ_r n' k)))).
    rewrite -> down_cast.
    rewrite -> (IHn' (down (S (n' + k)) x)).
    rewrite <- (down_iter_S (S n') k).
    reflexivity.
Qed.

Lemma shift_obligation_1 : forall (m n : nat), m <= n -> n - m + m = n.
Proof. exact Nat.sub_add. Qed.

Lemma shift_obligation_2 (m n : nat) (H_lt : n < m) : m = m - n + n.
Proof. symmetry. exact (Nat.sub_add n m (Nat.lt_le_incl n m H_lt)). Qed.

Definition shift (m n : nat) (x : approx m) : approx n :=
  match le_lt_dec m n with
  | left H_le => cast (n - m + m) n (shift_obligation_1 m n H_le) (up_iter (n - m) m x)
  | right H_lt => down_iter (m - n) n (cast m (m - n + n) (shift_obligation_2 m n H_lt) x)
  end.

Lemma shift_up (m n : nat) (x : approx m) : shift (S m) n (up m x) = shift m n x.
Proof.
  unfold shift.
  destruct (le_lt_dec (S m) n) as [H_le1 | H_lt1].
  - destruct (le_lt_dec m n) as [H_le2 | H_lt2].
    + assert (H_eq : exists p, S p = n).
      { exists (pred n).
        exact (Nat.lt_succ_pred _ _ (proj1 (Nat.le_succ_l m n) H_le1)). }
      destruct H_eq as [p H_eq].
      destruct H_eq as [].
      assert (H_le := proj2 (Nat.succ_le_mono m p) H_le1 : m <= p).
      assert (H_eq : S (p - m + m) = S p).
      { rewrite -> (Nat.sub_add m p H_le).
        reflexivity. }
      rewrite -> (UIP_nat _ _ _ (eq_trans (Nat.add_succ_r (p - m) m) H_eq)).
      rewrite <- cast_comp.
      rewrite -> (cast_up_iter_up (p - m) m).
      rewrite <- (cast_up_iter_l (S (p - m)) (S p - m) m (eq_sym (Nat.sub_succ_l m p H_le))).
      rewrite -> cast_comp.
      rewrite -> (UIP_nat _ _ (eq_trans _ _) H_eq).
      reflexivity.
    + contradict (Nat.lt_irrefl n (Nat.lt_trans n m n H_lt2 (proj1 (Nat.le_succ_l m n) H_le1))).
  - destruct (le_lt_dec m n) as [H_le2 | H_lt2].
    + destruct (Nat.le_antisymm n m (proj1 (Nat.lt_succ_r n m) H_lt1) H_le2 : n = m) as [].
      assert (H_eq := Nat.sub_diag n : n - n = O).
      assert (H_eq' : 1 = S n - n).
      { rewrite -> (Nat.sub_succ_l n n (Nat.le_refl n)).
        rewrite -> H_eq.
        reflexivity. }
      rewrite -> (UIP_nat _ _ _ (f_equal (fun p => p + n) H_eq')).
      rewrite -> (down_iter_cast_l (S n - n) 1 n).
      rewrite -> down_iter_S.
      rewrite -> down_iter_O.
      rewrite -> down_up.
      rewrite -> (UIP_nat _ _ _ (f_equal (fun p : nat => p + n) H_eq)).
      rewrite -> (cast_up_iter_l (n - n) O n).
      rewrite -> up_iter_O.
      reflexivity.
    + rewrite <- (down_iter_cast_l (S (m - n)) (S m - n) n (Nat.sub_succ_l n m (Nat.lt_le_incl n m H_lt2))).
      rewrite -> cast_comp.
      rewrite -> (UIP_nat _ _ _ (f_equal S (shift_obligation_2 m n H_lt2))).
      rewrite -> down_iter_S.
      rewrite -> (down_cast (m - n + n) m).
      rewrite -> down_up.
      reflexivity.
Qed.

Lemma down_shift (m n : nat) (x : approx m) : down n (shift m (S n) x) = shift m n x.
Proof.
  unfold shift.
  destruct (le_lt_dec m (S n)) as [H_le1 | H_lt1].
  - destruct (le_lt_dec m n) as [H_le2 | H_lt2].
    + rewrite <- (cast_up_iter_l (S (n - m)) (S n - m) m (eq_sym (Nat.sub_succ_l m n H_le2))).
      rewrite -> cast_comp.
      rewrite -> (UIP_nat _ _ _ (f_equal S (shift_obligation_1 m n H_le2))).
      rewrite -> up_iter_S.
      rewrite -> (cast_up (n - m + m) n).
      rewrite -> down_up.
      reflexivity.
    + destruct (Nat.le_antisymm _ _ H_lt2 H_le1 : S n = m) as [].
      assert (H_eq := Nat.sub_diag n : n - n = O).
      rewrite -> (UIP_nat _ _ _ (f_equal (fun p => p + S n) H_eq)).
      rewrite -> (cast_up_iter_l (n - n) O (S n)).
      rewrite -> up_iter_O.
      assert (H_eq' : 1 = S n - n).
      { rewrite -> (Nat.sub_succ_l n n (Nat.le_refl n)).
        rewrite -> H_eq.
        reflexivity. }
      rewrite -> (UIP_nat _ _ _ (f_equal (fun p => p + n) H_eq')).
      rewrite -> (down_iter_cast_l (S n - n) 1 n).
      rewrite -> down_iter_S.
      rewrite -> down_iter_O.
      reflexivity.
  - destruct (le_lt_dec m n) as [H_le2 | H_lt2].
    + contradict (Nat.lt_irrefl m (Nat.lt_trans m (S n) m (proj2 (Nat.lt_succ_r m n) H_le2) H_lt1)).
    + assert (H_eq : exists p, S p = m).
      { exists (pred m).
        exact (Nat.lt_succ_pred _ _ H_lt2). }
      destruct H_eq as [p H_eq].
      destruct H_eq as [].
      assert (H_le := proj1 (Nat.lt_succ_r n p) H_lt2 : n <= p).
      assert (H_eq : S p = S (p - n + n)).
      { rewrite -> (Nat.sub_add n p H_le).
        reflexivity. }
      rewrite -> (UIP_nat _ _ _ (eq_trans H_eq (eq_sym (Nat.add_succ_r (p - n) n)))).
      rewrite <- cast_comp.
      rewrite -> (down_down_iter_cast (p - n) n).
      rewrite <- (down_iter_cast_l (S (p - n)) (S p - n) n (Nat.sub_succ_l n p H_le)).
      rewrite -> cast_comp.
      rewrite -> (UIP_nat _ _ (eq_trans _ _) H_eq).
      reflexivity.
Qed.

Record tower : Type := { tower_car (k : nat) : approx k; down_tower (k : nat) : down k (tower_car (S k)) = tower_car k }.
Coercion tower_car : tower >-> Funclass.

Axiom tower_eq : forall (s t : tower), s = t <-> forall k, s k = t k.
Axiom tower_dist : forall (n : nat) (s t : tower), s ={n}= t <-> forall k, s k ={n}= t k.

Lemma up_tower (t : tower) (k : nat) : up (S k) (t (S k)) ={k}= t (S (S k)).
Proof.
  rewrite <- down_tower.
  rewrite -> up_down.
  reflexivity.
Qed.

Lemma up_iter_tower (t : tower) (n k : nat) : up_iter n (S k) (t (S k)) ={k}= t (n + S k).
Proof.
  induction n as [| n' IHn']; simpl.
  - reflexivity.
  - rewrite -> IHn'.
    rewrite -> Nat.add_succ_r.
    apply (dist_le (n' + k) k _ _ (Nat.le_add_l k n')).
    rewrite -> up_tower.
    reflexivity.
Qed.

Lemma down_iter_tower (t : tower) (n k : nat) : down_iter n k (t (n + k)) = t k.
Proof.
  induction n as [| n' IHn']; simpl.
  - reflexivity.
  - rewrite -> down_tower.
    rewrite -> IHn'.
    reflexivity.
Qed.

Lemma cast_tower (t : tower) (m n : nat) (H_eq : m = n) :
  cast m n H_eq (t m) = t n.
Proof.
  destruct H_eq as [].
  unfold cast. reflexivity.
Qed.

Lemma shift_tower (t : tower) (m n : nat) :
  shift (S m) n (t (S m)) ={m}= t n.
Proof.
  unfold shift.
  destruct (le_lt_dec (S m) n) as [H_le | H_lt].
  - rewrite -> up_iter_tower.
    rewrite -> cast_tower.
    reflexivity.
  - rewrite -> cast_tower.
    rewrite -> down_iter_tower.
    reflexivity.
Qed.

Lemma embed_obligation (k : nat) (x : approx k) (i : nat) : down i (shift k (S i) x) = shift k i x.
Proof. exact (down_shift k i x). Qed.

Definition embed (k : nat) (x : approx k) : tower :=
  {| tower_car (i : nat) := shift k i x; down_tower := embed_obligation k x |}.

Lemma embed_up (k : nat) (x : approx k) : embed (S k) (up k x) = embed k x.
Proof.
  apply tower_eq. intros i. simpl.
  exact (shift_up k i x).
Qed.

Lemma embed_tower (t : tower) (k : nat) : embed (S k) (t (S k)) ={k}= t.
Proof.
  apply tower_dist. intros i. simpl.
  exact (shift_tower t k i).
Qed.

Definition proj (k : nat) (t : tower) : approx k := t k.

Instance proj_NonExpansive (k : nat) : NonExpansive (proj k).
Proof.
  unfold NonExpansive, proj.
  intros n s t H_dist. exact (proj1 (tower_dist n s t) H_dist k).
Qed.

Lemma down_proj (k : nat) (t : tower) : down k (proj (S k) t) = proj k t.
Proof. unfold proj. exact (down_tower t k). Qed.

Lemma embed_proj (k : nat) (t : tower) : embed (S k) (proj (S k) t) ={k}= t.
Proof. unfold proj. exact (embed_tower t k). Qed.

Record chain (A : Type) : Type :=
  { chain_car : nat -> A;
    cauchy (n i : nat) : n <= i -> chain_car i ={n}= chain_car n }.

Coercion chain_car : chain >-> Funclass.
Arguments chain_car {A}.
Arguments cauchy {A}.

Lemma tower_chain_obligation (c : chain tower) (k n i : nat) (H_le : n <= i) : c i k ={n}= c n k.
Proof. exact (proj1 (tower_dist n (c i) (c n)) (cauchy c n i H_le) k). Qed.

Definition tower_chain (c : chain tower) (k : nat) : chain (approx k) :=
  {| chain_car (n : nat) := c n k; cauchy := tower_chain_obligation c k |}.

Class Complete A : Type :=
  { compl : chain A -> A;
    compl_conv (n : nat) (c : chain A) : compl c ={n}= c n }.

Parameter F_Complete : forall A, Complete A -> Complete (F A A).
Existing Instance F_Complete.

Lemma unit_Complete_obligation (n : nat) (c : chain unit) : tt ={n}= c n.
Proof. destruct (c n) as []. reflexivity. Qed.

Instance unit_Complete : Complete unit :=
  {| compl _ := tt; compl_conv := unit_Complete_obligation |}.

Fixpoint approx_Complete (k : nat) : Complete (approx k) :=
  match k with
  | O => unit_Complete
  | S k' => F_Complete (approx k') (approx_Complete k')
  end.

Existing Instance approx_Complete.

Lemma tower_compl_obligation (c : chain tower) (k : nat) :
  down k (compl (tower_chain c (S k))) = compl (tower_chain c k).
Proof.
  apply eq_dist. intros n.
  rewrite -> compl_conv.
  rewrite -> compl_conv. simpl.
  rewrite -> down_tower.
  reflexivity.
Qed.

Definition tower_compl (c : chain tower) : tower :=
  {| tower_car (k : nat) := compl (tower_chain c k); down_tower := tower_compl_obligation c |}.

Lemma tower_Complete_obligation (n : nat) (c : chain tower) :
  tower_compl c ={n}= c n.
Proof.
  apply tower_dist. intros k. simpl.
  rewrite -> compl_conv. simpl.
  reflexivity.
Qed.

Instance tower_Complete : Complete tower :=
  {| compl := tower_compl; compl_conv := tower_Complete_obligation |}.

Lemma unroll_chain_obligation (t : tower) (n : nat) :
  forall (i : nat), n <= i -> dimap (proj i) (embed i) (t (S i)) ={n}= dimap (proj n) (embed n) (t (S n)).
Proof.
  apply (Nat.right_induction _ _ n).
  - reflexivity.
  - intros i H_le IHi.
    rewrite <- IHi.
    apply (dist_le i n _ _ H_le).
    rewrite <- (up_tower t i).
    rewrite -> up_S.
    rewrite -> dimap_comp.
    rewrite -> (functional_extensionality _ _ (down_proj i)).
    rewrite -> (functional_extensionality _ _ (embed_up i)).
    reflexivity.
Qed.

Definition unroll_chain (t : tower) : chain (F tower tower) :=
  {| chain_car (n : nat) := dimap (proj n) (embed n) (t (S n)); cauchy := unroll_chain_obligation t |}.

Definition unroll (t : tower) : F tower tower :=
  compl (unroll_chain t).

Lemma roll_obligation (m : F tower tower) (k : nat) :
  down k (down (S k) (dimap (embed (S k)) (proj (S k)) m)) =
  down k (dimap (embed k) (proj k) m).
Proof.
  rewrite -> down_S.
  rewrite -> dimap_comp.
  rewrite -> (functional_extensionality _ _ (embed_up k)).
  rewrite -> (functional_extensionality _ _ (down_proj k)).
  reflexivity.
Qed.

Definition roll (m : F tower tower) : tower :=
  {| tower_car (k : nat) := down k (dimap (embed k) (proj k) m); down_tower := roll_obligation m |}.

Lemma dimap_up_iter_down_iter_tower (t : tower) (n k : nat) :
  dimap (up_iter n k) (down_iter n k) (t (S (n + k))) = t (S k).
Proof.
  induction n as [| n' IHn']; simpl.
  - rewrite -> dimap_id.
    reflexivity.
  - rewrite <- dimap_comp.
    rewrite <- (down_S (n' + k)).
    rewrite -> down_tower.
    rewrite -> IHn'.
    reflexivity.
Qed.

Lemma dimap_down_iter_up_iter_tower (t : tower) (n k : nat) :
  dimap (down_iter n k) (up_iter n k) (t (S k)) ={k}= t (S (n + k)).
Proof.
  induction n as [| n' IHn']; simpl.
  - rewrite -> dimap_id.
    reflexivity.
  - rewrite <- dimap_comp.
    rewrite <- (up_S (n' + k)).
    rewrite -> IHn'.
    apply (dist_le (n' + k) k _ _ (Nat.le_add_l k n')).
    rewrite -> up_tower.
    reflexivity.
Qed.

Lemma dimap_cast_cast_tower (t : tower) (m n : nat) (H_eq : m = n) :
  dimap (cast m n H_eq) (cast n m (eq_sym H_eq)) (t (S n)) = t (S m).
Proof.
  destruct H_eq as [].
  unfold cast, eq_sym.
  rewrite -> dimap_id.
  reflexivity.
Qed.

Lemma dimap_shift_shift_tower (t : tower) (m n : nat) :
  dimap (shift m n) (shift n m) (t (S n)) ={n}= t (S m).
Proof.
  unfold shift.
  destruct (le_lt_dec m n) as [H_le1 | H_lt1].
  - destruct (le_lt_dec n m) as [H_le2 | H_lt2].
    + destruct (Nat.le_antisymm _ _ H_le2 H_le1 : n = m) as [].
      assert (H_eq := Nat.sub_diag n : n - n = O).
      rewrite -> (le_unique _ _ H_le1 H_le2).
      rewrite -> (UIP_nat _ _ _ (f_equal (fun p : nat => p + n) H_eq)).
      rewrite -> (functional_extensionality (fun x => cast (n - n + n) n _ _) _  (cast_up_iter_l (n - n) O n H_eq)). simpl.
      rewrite -> dimap_id.
      reflexivity.
    + rewrite <- dimap_comp.
      rewrite -> (UIP_nat _ _ _ (eq_sym (shift_obligation_1 m n H_le1))).
      rewrite -> dimap_cast_cast_tower.
      rewrite -> dimap_up_iter_down_iter_tower.
      reflexivity.
  - destruct (le_lt_dec n m) as [H_le2 | H_lt2].
    + rewrite <- dimap_comp.
      rewrite -> dimap_down_iter_up_iter_tower.
      rewrite -> (UIP_nat _ _ _ (eq_sym (shift_obligation_2 m n H_lt1))).
      rewrite -> dimap_cast_cast_tower.
      reflexivity.
    + contradict (Nat.lt_irrefl n (Nat.lt_trans n m n H_lt1 H_lt2)).
Qed.

Lemma roll_unroll (t : tower) : roll (unroll t) = t.
Proof.
  apply eq_dist. intros n.
  apply tower_dist. intros k. simpl.
  unfold unroll.
  rewrite -> compl_conv. simpl.
  rewrite -> dimap_comp. simpl.
  rewrite -> dimap_shift_shift_tower.
  rewrite -> down_tower.
  reflexivity.
Qed.

Lemma unroll_roll (m : F tower tower) : unroll (roll m) = m.
Proof.
  apply eq_dist. intros n.
  unfold unroll.
  rewrite -> compl_conv. simpl.
  rewrite -> dimap_comp.
  rewrite -> dimap_comp.
  rewrite <- (dimap_id m) at 2.
  apply dist_ext.
  destruct n as [| n'].
  - exact (contractive2_dist_O _ _ _ _).
  - apply contractive2_dist_S.
    + apply dist_ext. intros t.
      rewrite -> embed_up.
      rewrite -> embed_proj.
      reflexivity.
    + apply dist_ext. intros t.
      rewrite -> down_proj.
      rewrite -> embed_proj.
      reflexivity.
Qed.
