From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope term_scope.

Example Map :=
  <{ fun "K" =>
       let "empty" := Inl () in
       let "is_empty" "m" :=
         match "m" with
         | Inl _ => true
         | Inr _ => false
         end
       in
       let "member" ("k", "m") :=
         let fix "go" "m" :=
           match "m" with
           | Inl _ => false
           | Inr `("l", "k'", _, "r", _) =>
               match by "K".`"compare" ("k", "k'") with
               | `"Lt" _ => "go" "l"
               | `"Eq" _ => true
               | `"Gt" _ => "go" "r"
               end
           end
         in
         "go" "m"
       in
       let "lookup" ("k", "m") :=
         let fix "go" "m" :=
           match "m" with
           | Inl _ => Inl ()
           | Inr `("l", "k'", "v", "r", _) =>
               match by "K".`"compare" ("k", "k'") with
               | `"Lt" _ => "go" "l"
               | `"Eq" _ => Inr "v"
               | `"Gt" _ => "go" "r"
               end
           end
         in
         "go" "m"
       in
       let "height" "m" :=
         match "m" with
         | Inl _ => 0
         | Inr `(_, _, _, _, "h") => "h"
         end
       in
       let "node" `("l", "k", "v", "r") :=
         let "hl" := "height" "l" in
         let "hr" := "height" "r" in
         Inr `("l", "k", "v", "r", (by if "hl" > "hr" then "hl" else "hr") + 1)
       in
       let "ne_unnode" "m" :=
         match "m" with
         | Inl _ => raise `"Empty" ()
         | Inr `("l", "k", "v", "r", _) => `("l", "k", "v", "r")
         end
       in
       let "balance" "args" :=
         let `("l", "k", "v", "r") := "args" in
         let "hl" := "height" "l" in
         let "hr" := "height" "r" in
         if "hl" > "hr" + 2 then
           let `("ll", "lk", "lv", "lr") := "ne_unnode" "l" in
           if by "height" "ll" >= by "height" "lr" then
             let "lr'" := "node" `("lr", "k", "v", "r") in
             "node" `("ll", "lk", "lv", "lr'")
           else
             let `("lrl", "lrk", "lrv", "lrr") := "ne_unnode" "lr" in
             let "lrl'" := "node" `("ll", "lk", "lv", "lrl") in
             let "lrr'" := "node" `("lrr", "k", "v", "r") in
             "node" `("lrl'", "lrk", "lrv", "lrr'")
         else
           if "hr" > "hl" + 2 then
             let `("rl", "rk", "rv", "rr") := "ne_unnode" "r" in
             if by "height" "rr" >= by "height" "rl" then
               let "rl'" := "node" `("l", "k", "v", "rl") in
               "node" `("rl'", "rk", "rv", "rr")
             else
               let `("rll", "rlk", "rlv", "rlr") := "ne_unnode" "rl" in
               let "rll'" := "node" `("l", "k", "v", "rll") in
               let "rlr'" := "node" `("rlr", "rk", "rv", "rr") in
               "node" `("rll'", "rlk", "rlv", "rlr'")
           else "node" "args"
       in
       let "singleton" ("k", "v") := Inr `(Inl (), "k", "v", Inl (), 1) in
       let "insert" `("k", "v", "m") :=
         let fix "go" "m" :=
           match "m" with
           | Inl _ => "singleton" ("k", "v")
           | Inr `("l", "k'", "v'", "r", "h") =>
               match by "K".`"compare" ("k", "k'") with
               | `"Lt" _ => "balance" `(by "go" "l", "k'", "v'", "r")
               | `"Eq" _ => Inr `("l", "k", "v", "r", "h")
               | `"Gt" _ => "balance" `("l", "k'", "v'", by "go" "r")
               end
           end
         in
         "go" "m"
       in
       let fix "min_binding_remove_aux" `("l", "k", "v", "r") :=
         match "l" with
         | Inl _ => (("k", "v"), "r")
         | Inr `("ll", "lk", "lv", "lr", _) =>
             let ("b", "l'") := "min_binding_remove_aux" `("ll", "lk", "lv", "lr") in
             ("b", by "balance" `("l'", "k", "v", "r"))
         end
       in
       let "min_binding_remove" "m" :=
         match "m" with
         | Inl _ => (Inl (), Inl ())
         | Inr `("l", "k", "v", "r", _) =>
             let ("b", "m'") := "min_binding_remove_aux" `("l", "k", "v", "r") in
             (Inr "b", "m'")
         end
       in
       let "link" ("m1", "m2") :=
         match "m1" with
         | Inl _ => "m2"
         | Inr _ =>
             match "m2" with
             | Inl _ => "m1"
             | Inr `("l2", "k2", "v2", "r2", _) =>
                 let (("k", "v"), "m2'") := "min_binding_remove_aux" `("l2", "k2", "v2", "r2") in
                 "balance" `("m1", "k", "v", "m2'")
             end
         end
       in
       let "remove" ("k", "m") :=
         let fix "go" "m" :=
           match "m" with
           | Inl _ => Inl ()
           | Inr `("l", "k'", "v", "r", _) =>
               match by "K".`"compare" ("k", "k'") with
               | `"Lt" _ => "balance" `(by "go" "l", "k'", "v", "r")
               | `"Eq" _ => "link" ("l", "r")
               | `"Gt" _ => "balance" `("l", "k'", "v", by "go" "r")
               end
           end
         in
         "go" "m"
       in
       `{ "empty"
        ; "is_empty"
        ; "member"
        ; "lookup"
        ; "singleton"
        ; "insert"
        ; "remove"
        ; "min_binding_remove" } }>.
