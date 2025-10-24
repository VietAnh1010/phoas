From shift_reset.core Require Import syntax.

Fixpoint kont_append (k1 k2 : kont) : kont :=
  match k1 with
  | KNil => k2
  | KCons c k1' => KCons c (kont_append k1' k2)
  end.

Definition metakont_extend (mk : metakont) (k : kont) : metakont :=
  match mk with
  | MKPure k' => MKPure (kont_append k' k)
  | MKReset mk' tag k' => MKReset mk' tag (kont_append k' k)
  | MKPrompt mk' tag k' => MKPrompt mk' tag (kont_append k' k)
  | MKTry mk' c k' => MKTry mk' c (kont_append k' k)
  | MKHandle mk' c k' => MKHandle mk' c (kont_append k' k)
  | MKShallowHandle mk' c k' => MKShallowHandle mk' c (kont_append k' k)
  end.

Definition MKTry' (mk : metakont) (t : exn_term) (k : kont) (env : env) : metakont :=
  MKTry mk (CTry env t) k.

Definition MKHandle' (mk : metakont) (t1 : ret_term) (t2 : eff_term) (k : kont) (env : env) : metakont :=
  MKHandle mk (CHandle env t1 t2) k.

Definition MKShallowHandle' (mk : metakont) (t1 : ret_term) (t2 : eff_term) (k : kont) (env : env) : metakont :=
  MKShallowHandle mk (CShallowHandle env t1 t2) k.
