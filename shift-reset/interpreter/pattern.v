From Stdlib Require Import Ascii String Qcanon ZArith.
From shift_reset.lib Require option.
From shift_reset.lib Require Import float.
From shift_reset.core Require Import syntax ident record.
From shift_reset.monad Require Import except.
From shift_reset.interpreter Require Import error imonad.
Import option.OptionNotations.

Local Open Scope option_scope.

Fixpoint match_pattern (p : pattern) (v : val) (e : env) : option env :=
  match p, v with
  | PAny, _ => Some e
  | PVar x, _ => Some (EnvCons x v e)
  | PAlias p' x, _ => EnvCons x v <$> match_pattern p' v e
  | POr p1 p2, _ =>
      match match_pattern p1 v e with
      | None => match_pattern p2 v e
      | Some e => Some e
      end
  | PTt, VTt => Some e
  | PInt z1, VInt z2 => if (z1 =? z2)%Z then Some e else None
  | PFloat q1, VFloat q2 => if (q1 =? q2)%Qc then Some e else None
  | PTrue, VTrue => Some e
  | PFalse, VFalse => Some e
  | PChar a1, VChar a2 => if (a1 =? a2)%char then Some e else None
  | PString s1, VString s2 => if (s1 =? s2)%string then Some e else None
  | PPair p1 p2, VPair v1 v2 => match_pattern p1 v1 e >>= match_pattern p2 v2
  | PTuple ps, VTuple vs => match_patterns ps vs e
  | PRecord p', VRecord r => match_record_pattern p' r e
  | PInl p', VInl v' => match_pattern p' v' e
  | PInr p', VInr v' => match_pattern p' v' e
  | PVariant l1 p', VVariant l2 v' => if ident_eqb l1 l2 then match_pattern p' v' e else None
  | PEnum l1, VEnum l2 => if ident_eqb l1 l2 then Some e else None
  | PNil, VNil => Some e
  | PCons p1 p2, VCons v1 v2 => match_pattern p1 v1 e >>= match_pattern p2 v2
  | _, _ => None
  end
with match_patterns (ps : patterns) (vs : vals) (e : env) : option env :=
  match ps, vs with
  | PsNil, VsNil => Some e
  | PsCons p ps', VsCons v vs' => match_pattern p v e >>= match_patterns ps' vs'
  | _, _ => None
  end
with match_record_pattern (p : record_pattern) (r : record) (e : env) : option env :=
  match p with
  | PRecordNil =>
      match r with
      | RecordNil => Some e
      | RecordCons _ _ _ => None
      end
  | PRecordRest p' => match_pattern p' (VRecord r) e
  | PRecordCons l p1 p2 =>
      let* '(v, r) := record_pop l r in
      match_pattern p1 v e >>= match_record_pattern p2 r
  | PRecordConsPun l p' =>
      let* '(v, r) := record_pop l r in
      match_record_pattern p' r (EnvCons l v e)
  end.

Definition match_irrefutable_pattern (p : pattern) (v : val) (e : env) : iv_monad env :=
  match match_pattern p v e with
  | None => throw (Match_failure v)
  | Some e => pure e
  end.
