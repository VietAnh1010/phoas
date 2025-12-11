Module Type T0.
  Parameter t : Type.
End T0.

Module Type T1.
  Parameter t : Type -> Type.
End T1.

Module Type Monoid.
  Include T0.
  Parameter empty : t.
  Parameter combine : t -> t -> t.
End Monoid.

Module Type Monad.
  Include T1.
  Parameter pure : forall {A}, A -> t A.
  Parameter map : forall {A B}, (A -> B) -> t A -> t B.
  Parameter app : forall {A B}, t (A -> B) -> t A -> t B.
  Parameter bind : forall {A B}, t A -> (A -> t B) -> t B.
End Monad.

Module Type MonadReader.
  Include Monad.
  Parameter r : Type.
  Parameter ask : t r.
  Parameter reader : forall {A}, (r -> A) -> t A.
  Parameter local : forall {A}, (r -> r) -> t A -> t A.
End MonadReader.

Module Type MonadWriter.
  Include Monad.
  Parameter w : Type.
  Parameter tell : w -> t unit.
  Parameter writer : forall {A}, (A * w) -> t A.
  Parameter listen : forall {A}, t A -> t (A * w).
  Parameter pass : forall {A}, t (A * (w -> w)) -> t A.
End MonadWriter.

Module Type MonadState.
  Include Monad.
  Parameter s : Type.
  Parameter get : t s.
  Parameter put : s -> t unit.
  Parameter state : forall {A}, (s -> A * s) -> t A.
End MonadState.

Module Type MonadExcept.
  Include Monad.
  Parameter e : Type.
  Parameter throw : forall {A}, e -> t A.
  Parameter catch : forall {A}, t A -> (e -> t A) -> t A.
End MonadExcept.

Module Identity <: Monad.
  Definition t (A : Type) : Type := A.
  Definition pure {A} (x : A) : t A := x.
  Definition map {A B} (f : A -> B) (m : t A) : t B := f m.
  Definition app {A B} (m1 : t (A -> B)) (m2 : t A) : t B := m1 m2.
  Definition bind {A B} (m : t A) (f : A -> t B) : t B := f m.
End Identity.

Module ReaderT (R : T0) (M : Monad) <: MonadReader.
  Definition r : Type := R.t.
  Definition m : Type -> Type := M.t.
  Definition t (A : Type) : Type := r -> m A.

  Definition pure {A} (x : A) : t A :=
    fun _ => M.pure x.

  Definition map {A B} (f : A -> B) (m : t A) : t B :=
    fun r => M.map f (m r).

  Definition app {A B} (m1 : t (A -> B)) (m2 : t A) : t B :=
    fun r => M.app (m1 r) (m2 r).

  Definition bind {A B} (m : t A) (f : A -> t B) : t B :=
    fun r => M.bind (m r) (fun x => (f x) r).

  Definition ask : t r :=
    M.pure.

  Definition reader {A} (f : r -> A) : t A :=
    fun r => M.pure (f r).

  Definition local {A} (f : r -> r) (m : t A) : t A :=
    fun r => (m (f r)).
End ReaderT.

Module Reader (R : T0) <: MonadReader := ReaderT R Identity.

Module LiftWriterReaderT (R : T0) (M : MonadWriter).
  Local Notation r := R.t.
  Local Notation m := M.t.
  Local Notation t A := (r -> m A).
  Definition w : Type := M.w.

  Definition tell (w : w) : t unit :=
    fun _ => M.tell w.

  Definition writer {A} (p : A * w) : t A :=
    fun _ => M.writer p.

  Definition listen {A} (m : t A) : t (A * w) :=
    fun r => M.listen (m r).

  Definition pass {A} (m : t (A * (w -> w))) : t A :=
    fun r => M.pass (m r).
End LiftWriterReaderT.

Module LiftStateReaderT (R : T0) (M : MonadState).
  Local Notation r := R.t.
  Local Notation m := M.t.
  Local Notation t A := (r -> m A).
  Definition s : Type := M.s.

  Definition get : t s :=
    fun _ => M.get.

  Definition put (s : s) : t unit :=
    fun _ => M.put s.

  Definition state {A} (f : s -> A * s) : t A :=
    fun _ => M.state f.
End LiftStateReaderT.

Module LiftExceptReaderT (R : T0) (M : MonadExcept).
  Local Notation r := R.t.
  Local Notation m := M.t.
  Local Notation t A := (r -> m A).
  Definition e : Type := M.e.

  Definition throw {A} (e : e) : t A :=
    fun _ => M.throw e.

  Definition catch {A} (m : t A) (f : e -> t A) : t A :=
    fun r => M.catch (m r) (fun e => (f e) r).
End LiftExceptReaderT.

Module WriterT (W : Monoid) (M : Monad) <: MonadWriter.
  Definition w : Type := W.t.
  Definition m : Type -> Type := M.t.
  Definition t (A : Type) : Type := m (A * w).

  Definition pure {A} (x : A) : t A :=
    M.pure (x, W.empty).

  Definition map {A B} (f : A -> B) (m : t A) : t B :=
    M.map (fun '(x, w) => (f x, w)) m.

  Definition app {A B} (m1 : t (A -> B)) (m2 : t A) : t B :=
    M.bind m1 (fun '(f, w1) => M.map (fun '(x, w2) => (f x, W.combine w1 w2)) m2).

  Definition bind {A B} (m : t A) (f : A -> t B) : t B :=
    M.bind m (fun '(x, w1) => M.map (fun '(y, w2) => (y, W.combine w1 w2)) (f x)).

  Definition tell (w : w) : t unit :=
    M.pure (tt, w).

  Definition writer {A} (p : A * w) : t A :=
    M.pure p.

  Definition listen {A} (m : t A) : t (A * w) :=
    M.map (fun '(x, w) => ((x, w), w)) m.

  Definition pass {A} (m : t (A * (w -> w))) : t A :=
    M.map (fun '((x, f), w) => (x, f w)) m.
End WriterT.

Module Writer (W : Monoid) <: MonadWriter := WriterT W Identity.

Module LiftReaderWriterT (W : Monoid) (M : MonadReader).
  Local Notation w := W.t.
  Local Notation m := M.t.
  Local Notation t A := (m (A * w)).
  Definition r : Type := M.r.

  Definition ask : t r :=
    M.map (fun r => (r, W.empty)) M.ask.

  Definition reader {A} (f : r -> A) : t A :=
    M.map (fun x => (x, W.empty)) (M.reader f).

  Definition local {A} : (r -> r) -> t A -> t A :=
    M.local.
End LiftReaderWriterT.

Module StateT (S : T0) (M : Monad) <: MonadState.
  Definition s : Type := S.t.
  Definition m : Type -> Type := M.t.
  Definition t (A : Type) : Type := s -> m (A * s).

  Definition pure {A} (x : A) : t A :=
    fun s => M.pure (x, s).

  Definition map {A B} (f : A -> B) (m : t A) : t B :=
    fun s => M.map (fun '(x, s) => (f x, s)) (m s).

  Definition app {A B} (m1 : t (A -> B)) (m2 : t A) : t B :=
    fun s => M.bind (m1 s) (fun '(f, s) => M.map (fun '(x, s) => (f x, s)) (m2 s)).

  Definition bind {A B} (m : t A) (f : A -> t B) : t B :=
    fun s => M.bind (m s) (fun '(x, s) => (f x) s).

  Definition get : t s :=
    fun s => M.pure (s, s).

  Definition put (s : s) : t unit :=
    fun _ => M.pure (tt, s).

  Definition state {A} (f : s -> A * s) : t A :=
    fun s => M.pure (f s).
End StateT.

Module State (S : T0) <: MonadState := StateT S Identity.

Module LiftReaderStateT (S : T0) (M : MonadReader).
  Local Notation s := S.t.
  Local Notation m := M.t.
  Local Notation t A := (s -> m (A * s)).
  Definition r : Type := M.r.

  Definition ask : t r :=
    fun s => M.map (fun r => (r, s)) M.ask.

  Definition reader {A} (f : r -> A) : t A :=
    fun s => M.map (fun x => (x, s)) (M.reader f).

  Definition local {A} (f : r -> r) (m : t A) : t A :=
    fun s => M.local f (m s).
End LiftReaderStateT.

Module ExceptT (E : T0) (M : Monad) <: MonadExcept.
  Definition e : Type := E.t.
  Definition m : Type -> Type := M.t.
  Definition t (A : Type) : Type := m (e + A).

  Definition pure {A} (x : A) : t A :=
    M.pure (inr x).

  Definition map {A B} (f : A -> B) (m : t A) : t B :=
    M.map (fun m => match m with
                    | inl e => inl e
                    | inr x => inr (f x)
                    end) m.

  Definition app {A B} (m1 : t (A -> B)) (m2 : t A) : t B :=
    M.bind m1 (fun m => match m with
                        | inl e => M.pure (inl e)
                        | inr f => M.map (fun m => match m with
                                                   | inl e => inl e
                                                   | inr x => inr (f x)
                                                   end) m2
                        end).

  Definition bind {A B} (m : t A) (f : A -> t B) : t B :=
    M.bind m (fun m => match m with
                       | inl e => M.pure (inl e)
                       | inr x => f x
                       end).

  Definition throw {A} (e : e) : t A :=
    M.pure (inl e).

  Definition catch {A} (m : t A) (f : e -> t A) : t A :=
    M.bind m (fun m => match m with
                       | inl e => f e
                       | inr _ => M.pure m
                       end).
End ExceptT.

Module Except (E : T0) <: MonadExcept := ExceptT E Identity.


