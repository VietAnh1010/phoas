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
           | Inr `("l", "k'", "v", "r", _) =>
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
       let "create" `("l", "k", "v", "r") :=
         let "hl" := "height" "l" in
         let "hr" := "height" "r" in
         Inr `("l", "k", "v", "r", (by if "hl" > "hr" then "hl" else "hr") + 1)
       in
       let "singleton" ("k", "v") := Inr `(Inl (), "k", "v", Inl (), 1) in
       let "ne_unnode" "m" :=
         match "m" with
         | Inl _ => raise `"Empty" ()
         | Inr "n" => "n"
         end
       in
       let "balance" "args" :=
         let `("l", "k", "v", "r") := "args" in
         let "hl" := "height" "l" in
         let "hr" := "height" "r" in
         if "hl" > "hr" + 2 then
           let `("ll", "lk", "lv", "lr", _) := "ne_unnode" "l" in
           if by "height" "ll" > by "height" "lr" then
             "create" `("ll", "lk", "lv", by "create" `("lr", "k", "v", "r"))
           else
             let `("lrl", "lrk", "lrv", "lrr", _) := "ne_unnode" "lr" in
             "create" `(by "create" `("ll", "lk", "lv", "lrl"), "lrk", "lrv", by "create" `("lrr", "k", "v", "r"))
         else
           if "hr" > "hl" + 2 then
             let `("rl", "rk", "rv", "rr", _) := "ne_unnode" "r" in
             if by "height" "rr" > by "height" "rl" then
               "create" `(by "create" `("l", "k", "v", "rl"), "rk", "rv", "rr")
             else
               let `("rll", "rlk", "rlv", "rlr", _) := "ne_unnode" "rl" in
               "create" `(by "create" `("l", "k", "v", "rll"), "rlk", "rlv", by "create" `("rlr", "rk", "rv", "rr"))
           else "create" "args"
       in
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
       `{ "empty"
        ; "is_empty"
        ; "member"
        ; "lookup"
        ; "insert" } }>.
