From Stdlib Require Import Bool String Qcanon ZArith.
From shift_reset.core Require Import syntax env loc record tag tuple var.
From shift_reset.monad Require except es_monad ers_monad.
From shift_reset.interpreter Require Import array builtin ierror iheap op unwrap.

Import es_monad.ESMonadNotations.
Import ers_monad.ERSMonadNotations.

Local Open Scope Z_scope.
Local Open Scope ers_monad_scope.
Local Open Scope lazy_bool_scope.

Definition transform {E R S A} (m : except.t E A) : ers_monad.t E R S A :=
  ers_monad.except (except.run_except m).

Fixpoint interpret_val_term (t : val_term) : ers_monad.t exn env iheap val :=
  match t with
  | TVVar x =>
      let* e := ers_monad.ask in
      match env_lookup x e with
      | None => ers_monad.throw (Name_error (var_car x))
      | Some v => ers_monad.pure v
      end
  | TVTt => ers_monad.pure VTt
  | TVInt z => ers_monad.pure (VInt z)
  | TVFloat q => ers_monad.pure (VFloat q)
  | TVTrue => ers_monad.pure VTrue
  | TVFalse => ers_monad.pure VFalse
  | TVChar a => ers_monad.pure (VChar a)
  | TVString s => ers_monad.pure (VString s)
  | TVAnd t1 t2 =>
      let* v := interpret_val_term t1 in
      let* b := transform (unwrap_vbool v) in
      if b then interpret_val_term t2 else ers_monad.pure VFalse
  | TVOr t1 t2 =>
      let* v := interpret_val_term t1 in
      let* b := transform (unwrap_vbool v) in
      if b then ers_monad.pure VTrue else interpret_val_term t2
  | TVFun b t' => ers_monad.reader (VFun b t')
  | TVFix f b t' => ers_monad.reader (VFix f b t')
  | TVFixMut t' f => ers_monad.reader (VFixMut t' f)
  | TVPair t1 t2 =>
      let* v := interpret_val_term t1 in
      VPair v <$> interpret_val_term t2
  | TVFst t' =>
      let* v := interpret_val_term t' in
      fst <$> transform (unwrap_vprod v)
  | TVSnd t' =>
      let* v := interpret_val_term t' in
      snd <$> transform (unwrap_vprod v)
  | TVTuple t' => VTuple <$> interpret_tuple_term t'
  | TVRecord t' => VRecord <$> interpret_record_term t'
  | TVProj t' tag =>
      let* v := interpret_val_term t' in
      let* r := transform (unwrap_vrecord v) in
      match record_lookup tag r with
      | None => ers_monad.throw (Name_error (tag_car tag))
      | Some v' => ers_monad.pure v'
      end
  | TVInl t' => VInl <$> interpret_val_term t'
  | TVInr t' => VInr <$> interpret_val_term t'
  | TVVariant tag t' => VVariant tag <$> interpret_val_term t'
  | TVRef t' =>
      let* v := interpret_val_term t' in
      ers_monad.state (fun h => (VRef (iheap_next_loc h), iheap_alloc v h))
  | TVGet t' =>
      let* v := interpret_val_term t' in
      let* l := transform (unwrap_vref v) in
      let* h := ers_monad.get in
      match iheap_read l h with
      | None => ers_monad.throw (Memory_error "ref_get")
      | Some v' => ers_monad.pure v'
      end
  | TVSet t1 t2 =>
      let* v1 := interpret_val_term t1 in
      let* v2 := interpret_val_term t2 in
      let* l := transform (unwrap_vref v1) in
      let* h := ers_monad.get in
      match iheap_write l v2 h with
      | None => ers_monad.throw (Memory_error "ref_set")
      | Some h' => VTt <$ ers_monad.put h'
      end
  | TVGetAt t1 t2 =>
      let* v1 := interpret_val_term t1 in
      let* v2 := interpret_val_term t2 in
      let* '(Array l z) := transform (unwrap_varray v1) in
      let* i := transform (unwrap_vint v2) in
      if (i <? 0) ||| (z <=? i) then
        ers_monad.throw (Invalid_argument "index out of bounds")
      else
        let* h := ers_monad.get in
        match iheap_read (loc_add l (Z.to_N i)) h with
        | None => ers_monad.throw (Memory_error "array_get_at")
        | Some v => ers_monad.pure v
        end
  | TVSetAt t1 t2 t3 =>
      let* v1 := interpret_val_term t1 in
      let* v2 := interpret_val_term t2 in
      let* v3 := interpret_val_term t3 in
      let* '(Array l z) := transform (unwrap_varray v1) in
      let* i := transform (unwrap_vint v2) in
      if (i <? 0) ||| (z <=? i) then
        ers_monad.throw (Invalid_argument "index out of bounds")
      else
        let* h := ers_monad.get in
        match iheap_write (loc_add l (Z.to_N i)) v3 h with
        | None => ers_monad.throw (Memory_error "array_set_at")
        | Some h' => VTt <$ ers_monad.put h'
        end
  | TVExn tag t' => VExn tag <$> interpret_val_term t'
  | TVEff tag t' => VEff tag <$> interpret_val_term t'
  | TVAssert t' =>
      let* v := interpret_val_term t' in
      let* b := transform (unwrap_vbool v) in
      if b then ers_monad.pure VTt else ers_monad.throw (Assert_failure "")
  | TVArray t' =>
      let* t := interpret_tuple_term t' in
      ers_monad.state (fun h => (VArray (iheap_next_loc h) (Z.of_nat (tuple_length t)), array_of_tuple_alloc t h))
  | TVOp1 op t' =>
      let* v := interpret_val_term t' in
      transform (dispatch_op1 op v)
  | TVOp2 op t1 t2 =>
      let* v1 := interpret_val_term t1 in
      let* v2 := interpret_val_term t2 in
      transform (dispatch_op2 op v1 v2)
  | TVBuiltin1 tag t' =>
      let* f := transform (dispatch_builtin1 tag) in
      let* v := interpret_val_term t' in
      ers_monad.ERSMonad (fun _ => es_monad.run_es_monad (f v))
  | TVBuiltin2 tag t1 t2 =>
      let* f := transform (dispatch_builtin2 tag) in
      let* v1 := interpret_val_term t1 in
      let* v2 := interpret_val_term t2 in
      ers_monad.ERSMonad (fun _ => es_monad.run_es_monad (f v1 v2))
  end
with interpret_tuple_term (t : tuple_term) : ers_monad.t exn env iheap tuple :=
  match t with
  | TTupleNil => ers_monad.pure TupleNil
  | TTupleCons t1 t2 =>
      let* v := interpret_val_term t1 in
      TupleCons v <$> interpret_tuple_term t2
  end
with interpret_record_term (t : record_term) : ers_monad.t exn env iheap record :=
  match t with
  | TRecordNil => ers_monad.pure RecordNil
  | TRecordCons tag t1 t2 =>
      let* v := interpret_val_term t1 in
      RecordCons tag v <$> interpret_record_term t2
  end.

Definition with_binder (b : binder) (v : val) (e : env) : env :=
  match b with
  | BAny => e
  | BVar x => ECons x v e
  end.

Definition match_variant (p : variant_pattern) (v : variant) (e : env) : option env :=
  let (tag, v) := v in
  match p with
  | PVariantAny => Some e
  | PVariantVar x => Some (ECons x (VVariant tag v) e)
  | PVariantTag tag' b => if tag_eqb tag tag' then Some (with_binder b v e) else None
  end.

Definition match_exn (p : variant_pattern) (exn : exn) (e : env) : option env :=
  let (tag, v) := exn in
  match p with
  | PVariantAny => Some e
  | PVariantVar x => Some (ECons x (VExn tag v) e)
  | PVariantTag tag' b => if tag_eqb tag tag' then Some (with_binder b v e) else None
  end.

Definition match_eff (p : variant_pattern) (tag : tag) (v : val) (e : env) : option env :=
  match p with
  | PVariantAny => Some e
  | PVariantVar x => Some (ECons x (VEff tag v) e)
  | PVariantTag tag' b => if tag_eqb tag tag' then Some (with_binder b v e) else None
  end.

Fixpoint match_tuple (p : tuple_pattern) (t : tuple) (e : env) : option env :=
  match p with
  | PTupleNil =>
      match t with
      | TupleNil => Some e
      | TupleCons _ _ => None
      end
  | PTupleCons b p' =>
      match t with
      | TupleNil => None
      | TupleCons v t' => match_tuple p' t' (with_binder b v e)
      end
  end.

Fixpoint match_record (p : record_pattern) (r : record) (e : env) : option env :=
  match p with
  | PRecordAny => Some e
  | PRecordVar x => Some (ECons x (VRecord r) e)
  | PRecordNil =>
      match r with
      | RecordNil => Some e
      | RecordCons _ _ _ => None
      end
  | PRecordCons tag b p' =>
      let (o, r') := record_lookup_remove tag r in
      match o with
      | Some v => match_record p' r' (with_binder b v e)
      | None => None
      end
  end.

Definition with_for_direction (d : for_direction) (i1 i2 : Z) : (Z -> Z) * Z :=
  match d with
  | Upto => (Z.succ, i2 - i1)
  | Downto => (Z.pred, i1 - i2)
  end.

Definition with_fix_mut_term (t : fix_mut_term) (e : env) : env :=
  let fix go t' e' :=
    match t' with
    | TFixMutLast f _ _ => ECons f (VFixMut t f e) e'
    | TFixMutCons f _ _ t'' => go t'' (ECons f (VFixMut t f e) e')
    end
  in
  go t e.

Notation ienv := (env * kont)%type.

Inductive iresult : Type :=
| IRShift : metakont -> (val -> ers_monad.t iresult ienv iheap val) -> iresult
| IRControl : metakont -> (val -> ers_monad.t iresult ienv iheap val) -> iresult
| IRRaise : exn -> iresult
| IRPerform : metakont -> eff -> iresult.

Definition imonad : Type -> Type := ers_monad.t iresult ienv iheap.
Definition interpreter : Type := term -> imonad val.

Definition interpret_ret_term_under (e : ienv) (self : interpreter) (t : ret_term) (v : val) :  imonad val :=
  match t with
  | TRetNone => ers_monad.pure v
  | TRetSome b t' => ers_monad.scope (with_binder b v (fst e), snd e) (self t')
  end.

Fixpoint interpret_exn_term_under (e : ienv) (self : interpreter) (t : exn_term) (exn : exn) : option (imonad val) :=
  let (e', k) := e in
  match t with
  | TExnLast p t' =>
      match match_exn p exn e' with
      | Some e' => Some (ers_monad.scope (e', k) (self t'))
      | None => None
      end
  | TExnCons p t1 t2 =>
      match match_exn p exn e' with
      | Some e' => Some (ers_monad.scope (e', k) (self t1))
      | None => interpret_exn_term_under e self t2 exn
      end
  end.

(*
Fixpoint interpret_eff_term_under (e : ienv) (self : interpreter) (t : eff_term) (k : kont) (tag : tag) (v u : val) : option (imonad val) :=
  match t with
  | TEffLast p b t' =>
      match match_eff p tag v e with
      | Some e' => Some (imonad_under (with_binder b u e') (self t' k))
      | None => None
      end
  | TEffCons p b t1 t2 =>
      match match_eff p tag v e with
      | Some e' => Some (imonad_under (with_binder b u e') (self t1 k))
      | None => interpret_eff_term_under e self t2 k tag v u
      end
  end.
*)

Fixpoint unwind_reset (k : kont) (r : iresult) : imonad val :=
  match r with
  | IRShift mk f => ers_monad.catch (f (VMKReset mk)) (unwind_reset k)
  | IRControl mk f => ers_monad.throw (IRControl (MKReset mk k) f)
  | IRRaise _ => ers_monad.throw r
  | IRPerform mk eff => ers_monad.throw (IRPerform (MKReset mk k) eff)
  end.

Fixpoint unwind_prompt (k : kont) (r : iresult) : imonad val :=
  match r with
  | IRShift mk f => ers_monad.throw (IRShift (MKPrompt mk k) f)
  | IRControl mk f => ers_monad.catch (f (VMKPure mk)) (unwind_prompt k)
  | IRRaise _ => ers_monad.throw r
  | IRPerform mk eff => ers_monad.throw (IRPerform (MKPrompt mk k) eff)
  end.

Definition unwind_try (self : interpreter) (t : exn_term) (r : iresult) : imonad val :=
  let* '((e, k) as ie) := ers_monad.ask in
  match r with
  | IRShift mk f => ers_monad.throw (IRShift (MKTry mk t e k) f)
  | IRControl mk f => ers_monad.throw (IRControl (MKTry mk t e k) f)
  | IRRaise exn =>
      match interpret_exn_term_under ie self t exn with
      | Some m => m
      | None => ers_monad.throw r
      end
  | IRPerform mk eff => ers_monad.throw (IRPerform (MKTry mk t e k) eff)
  end.

Definition unwind_handle (self : interpreter) (t1 : ret_term) (t2 : eff_term) (r : iresult) : imonad val :=
  let* '((e, k) as ie) := ers_monad.ask in
  match r with
  | IRShift mk f => ers_monad.throw (IRShift (MKHandle mk t1 t2 e k) f)
  | IRControl mk f => ers_monad.throw (IRControl (MKHandle mk t1 t2 e k) f)
  | IRRaise _ => ers_monad.throw r
  | IRPerform mk e => ers_monad.throw r
                        (*
      match interpret_eff_term_under e self t2 k tag v (VMKHandle mk t1 t2 e) with
      | Some m => m
      | None => ers_monad.throw (IRPerform (MKHandle mk t1 t2 e k) tag v)
      end*)
  end.

Definition unwind_shallow_handle (e : env) (self : interpreter) (t1 : ret_term) (t2 : eff_term) (k : kont) (r : iresult) : imonad3 :=
  match r with
  | IRShift mk f => imonad_throw (IRShift (MKShallowHandle mk t1 t2 e k) f)
  | IRControl mk f => imonad_throw (IRControl (MKShallowHandle mk t1 t2 e k) f)
  | IRRaise _ _ => imonad_throw r
  | IRPerform mk tag v =>
      match interpret_eff_term_under e self t2 k tag v (VMKPure mk) with
      | Some m => m
      | None => imonad_throw (IRPerform (MKShallowHandle mk t1 t2 e k) tag v)
      end
  end.
*)

Fixpoint interpret_kont_app (self : interpreter) (k1 : kont) (k2 : kont) (v : val) : imonad val :=
  match k1 with
  | KNil => ers_monad.pure v
  | KCons0 t e k1' => ers_monad.scope (e, KApp k1' k2) (self t) >>= interpret_kont_app self k1' k2
  | KCons1 b t e k1' => ers_monad.scope (with_binder b v e, KApp k1' k2) (self t) >>= interpret_kont_app self k1' k2
  | KApp k11 k12 => interpret_kont_app self k11 (KApp k12 k2) v >>= interpret_kont_app self k12 k2
  end.

Fixpoint interpret_kont (self : interpreter) (k : kont) (v : val) : imonad val :=
  match k with
  | KNil => ers_monad.pure v
  | KCons0 t e k' => ers_monad.scope (e, k') (self t) >>= interpret_kont self k'
  | KCons1 b t e k' => ers_monad.scope (with_binder b v e, k') (self t) >>= interpret_kont self k'
  | KApp k1 k2 => interpret_kont_app self k1 k2 v >>= interpret_kont self k2
  end.
(*
Definition refine_kont (self : interpreter) (k : kont) : ikont :=
  IKont k (interpret_kont self k).

Definition refine_kont_app (self : interpreter) (k1 : kont) (k2 : ikont) : ikont :=
  IKont (KApp k1 k2) (interpret_kont_app self k1 k2).
*)

(*
Fixpoint interpret_metakont (self : interpreter) (mk : metakont) (v : val) : imonad3 :=
  match mk with
  | MKPure k => interpret_kont self k v
  | MKReset mk' k => imonad_catch (interpret_metakont self mk' v) (unwind_reset k)
  | MKPrompt mk' k => imonad_catch (interpret_metakont self mk' v) (unwind_prompt k)
  | MKTry mk' t e k => imonad_catch (interpret_metakont self mk' v) (unwind_try e self t k)
  | MKHandle mk' t1 t2 e k =>
      imonad_catch (interpret_metakont self mk' v >>= interpret_ret_term_under e self t1 k) (unwind_handle e self t1 t2 k)
  | MKShallowHandle mk' t1 t2 e k =>
      imonad_catch (interpret_metakont self mk' v >>= interpret_ret_term_under e self t1 k) (unwind_shallow_handle e self t1 t2 k)
  end.
*)

(*
Definition interpret_metakont_app (self : interpreter) (mk : metakont) (k : ikont) (v : val) : imonad iresult :=
  match mk with
  | MKPure k' => interpret_kont_app self k' k v
  | MKReset mk' k' => interpret_metakont self mk' v >>= unwind_reset (refine_kont_app self k' k)
  | MKPrompt mk' k' => interpret_metakont self mk' v >>= unwind_prompt (refine_kont_app self k' k)
  | MKTry mk' t e k' => interpret_metakont self mk' v >>= unwind_try e self t (refine_kont_app self k' k)
  | MKHandle mk' t1 t2 e k' => interpret_metakont self mk' v >>= unwind_handle e self t1 t2 (refine_kont_app self k' k)
  | MKShallowHandle mk' t1 t2 e k' => interpret_metakont self mk' v >>= unwind_shallow_handle e self t1 t2 (refine_kont_app self k' k)
  end.
*)

Fixpoint interpret_variant_term (self : interpreter) (t : variant_term) (v : variant) : imonad val :=
  let* '(e, k) := ers_monad.ask in
  match t with
  | TVariantNil => ers_monad.throw (IRRaise (Match_failure ""))
  | TVariantCons p t1 t2 =>
      match match_variant p v e with
      | Some e' => ers_monad.scope (e', k) (self t1)
      | None => interpret_variant_term self t2 v
      end
  end.

(*
Fixpoint interpret_fix_mut_term_under (e : env) (self : interpreter) (t : fix_mut_term) (k : ikont) (f : var) (v : val) : imonad iresult :=
  match t with
  | TFixMutLast f' b t' =>
      if var_eqb f f'
      then imonad_under_env (with_binder b v e) (self t' k)
      else imonad_throw_error (Name_error (var_car f))
  | TFixMutCons f' b t1 t2 =>
      if var_eqb f f'
      then imonad_under_env (with_binder b v e) (self t1 k)
      else interpret_fix_mut_term_under e self t2 k f v
  end.
*)

Axiom cast : forall {A B}, A -> B.

Axiom cast' : forall {A}, except.t exn A -> imonad A.

Definition interpret_term (self : interpreter) : term -> imonad val :=
  fix self' t :=
    match t with
    | TVal tv => cast (interpret_val_term tv)
    | TApp tv1 tv2 =>
        ers_monad.throw (IRRaise (Failure "todo"))
        (*
        let* v1 := interpret_val_term tv1 in
        let* v2 := interpret_val_term tv2 in
        let* c := unwrap_vclosure v1 in
        match c with
        | CFun b t' e => imonad_under_env (with_binder b v2 e) (self t' k)
        | CFix f b t' e => imonad_under_env (with_binder b v2 (ECons f v1 e)) (self t' k)
        | CFixMut t' f e => interpret_fix_mut_term_under (with_fix_mut_term t' e) self t' k f v2
        | CMKPure mk => interpret_metakont_app self mk k v2
        | CMKReset mk => interpret_metakont self mk v2 >>= unwind_reset k
        | CMKHandle mk t1 t2 e => interpret_metakont self mk v2 >>= unwind_handle e self t1 t2 k
        end*)
    | TSeq t1 t2 =>
        let* '(e, k) := ers_monad.ask in
        let* _ := ers_monad.scope (e, KCons0 t2 e k) (self' t1) in
        ers_monad.scope (e, k) (self' t2)
    | TLet b t1 t2 =>
        let* '(e, k) := ers_monad.ask in
        let* v := ers_monad.scope (e, KCons1 b t2 e k) (self' t1) in
        ers_monad.scope (with_binder b v e, k) (self' t2)
    | TIf tv t1 t2 =>
        let* v := cast (interpret_val_term tv) in
        let* b := cast' (unwrap_vbool v) in
        if b then self' t1 else self' t2
    | TSplit b1 b2 tv t' =>
        let* v := cast (interpret_val_term tv) in
        let* '(v1, v2) := cast' (unwrap_vprod v) in
        ers_monad.local (fun '(e, k) => (with_binder b2 v2 (with_binder b1 v1 e), k)) (self' t')
    | TCase tv b1 t1 b2 t2 =>
        let* v := cast (interpret_val_term tv) in
        let* s := cast' (unwrap_vsum v) in
        match s with
        | inl v' => ers_monad.local (fun '(e, k) => (with_binder b1 v' e, k)) (self' t1)
        | inr v' => ers_monad.local (fun '(e, k) => (with_binder b2 v' e, k)) (self' t2)
        end
    | TMatchVariant tv t' =>
        let* v := cast (interpret_val_term tv) in
        cast' (unwrap_vvariant v) >>= interpret_variant_term self' t'
    | TWhile tv t' =>
        let* v := cast (interpret_val_term tv) in
        let* b := cast' (unwrap_vbool v) in
        if b then
          let* _ := ers_monad.local (fun '(e, k) => (e, KCons0 t e k)) (self' t') in
          self t
        else
          ers_monad.pure VTt
    | TShift b t' =>
        let* '(e, k) := ers_monad.ask in
        ers_monad.throw (IRShift (MKPure k) (fun u => ers_monad.scope (with_binder b u e, KNil) (self' t')))
    | TReset t' =>
        let* '(e, k) := ers_monad.ask in
        ers_monad.catch (ers_monad.scope (e, KNil) (self' t')) (unwind_reset k)
    | TControl b t' =>
        let* '(e, k) := ers_monad.ask in
        ers_monad.throw (IRControl (MKPure k) (fun u => ers_monad.scope (with_binder b u e, KNil) (self' t')))
    | TPrompt t' =>
        let* '(e, k) := ers_monad.ask in
        ers_monad.catch (ers_monad.scope (e, KNil) (self' t')) (unwind_reset k)
    | TRaise tv =>
        let* v := cast (interpret_val_term tv) in
        let* e := cast' (unwrap_vexn v) in
        ers_monad.throw (IRRaise e)
    | TTry t1 t2 =>
        ers_monad.catch (ers_monad.local (fun '(e, _) => (e, KNil)) (self' t1)) (unwind_try self t2)
    | TPerform tv =>
        let* v := cast (interpret_val_term tv) in
        let* e := cast' (unwrap_veff v) in
        let* '(_, k) := ers_monad.ask in
        ers_monad.throw (IRPerform (MKPure k) e)
    | _ =>
        ers_monad.throw (IRRaise (Failure "todo"))
    end.
(*
    | TFor b tv1 d tv2 t' =>
        let* v1 := interpret_val_term tv1 in
        let* v2 := interpret_val_term tv2 in
        let* i1 := unwrap_vint v1 in
        let* i2 := unwrap_vint v2 in
        let* e := imonad_ask_env in
        let tv := TVInt i2 in
        let (f, z) := with_for_direction d i1 i2 in
        let fix go n i :=
          match n with
          | O => ikont_app k VTt
          | S n' =>
          let i' := f i in
              imonad_under_env (with_binder b (VInt i) e) (self' t' (IKont (KCons0 (TFor b (TVInt i') d tv t') e k) (fun _ => go n' i')))
          end
        in
        go (Z.to_nat (Z.succ z)) i1
    | TLetFix f b t1 t2 => imonad_local_env (fun e => ECons f (VFix f b t1 e) e) (self' t2 k)
    | TLetFixMut t1 t2 => imonad_local_env (with_fix_mut_term t1) (self' t2 k)
    | TLetTuple p tv t' =>
        let* v := interpret_val_term tv in
        let* t := unwrap_vtuple v in
        let* e := imonad_ask_env in
        match match_tuple p t e with
        | Some e' => imonad_under_env e' (self' t' k)
        | None => imonad_throw_error (Match_failure "")
        end
    | TLetRecord p tv t' =>
        let* v := interpret_val_term tv in
        let* r := unwrap_vrecord v in
        let* e := imonad_ask_env in
        match match_record p r e with
        | Some e' => imonad_under_env e' (self' t' k)
        | None => imonad_throw_error (Match_failure "")
        end
    | THandle t1 t2 t3 =>
        let* r := self' t1 ikont_nil in
        let* e := imonad_ask_env in
        unwind_handle e self' t2 t3 k r
    | TShallowHandle t1 t2 t3 =>
        let* r := self' t1 ikont_nil in
        let* e := imonad_ask_env in
        unwind_shallow_handle e self' t2 t3 k r
    end.
*)

Fixpoint interpret_term' (fuel : nat) (t : term) : imonad val :=
  match fuel with
  | O => ers_monad.throw (IRRaise Out_of_fuel)
  | S fuel' => interpret_term (interpret_term' fuel') t
  end.

(*
Definition unwrap_IRVal (r : iresult) : imonad val :=
  match r with
  | IRShift _ _ => imonad_throw_error Undelimited_shift
  | IRControl _ _ => imonad_throw_error Undelimited_control
  | IRRaise _ _ => imonad_throw_error (Unhandled_exception "")
  | IRPerform _ _ _ => imonad_throw_error (Unhandled_effect "")
  end.
*)

(*
Definition run_term (fuel : nat) (t : term) : (ierror + val) * iheap :=
  imonad_run (interpret_term' fuel t ikont_nil >>= unwrap_IRVal) ENil iheap_empty.

Definition eval_term (fuel : nat) (t : term) : ierror + val :=
  fst (run_term fuel t).

Definition exec_term (fuel : nat) (t : term) : iheap :=
  snd (run_term fuel t).
*)
