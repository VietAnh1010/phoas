From Stdlib Require Import String.
From shift_reset.core Require Import syntax syntax_notation coerce.

Local Open Scope string_scope.
Local Open Scope term_scope.

Example Complex :=
  <{ let "neg" `{"re"; "im"} := `{"re" := -"re"; "im" := -"im"} in
     let "conj" `{"re"; "im"} := `{"re"; "im" := -"im"} in
     let "add" (`{"re" := "re1"; "im" := "im1"}, `{"re" := "re2"; "im" := "im2"}) :=
       `{"re" := "re1" + "re2"; "im" := "im1" + "im2"}
     in
     let "sub" (`{"re" := "re1"; "im" := "im1"}, `{"re" := "re2"; "im" := "im2"}) :=
       `{"re" := "re1" - "re2"; "im" := "im1" - "im2"}
     in
     let "norm2" `{"re"; "im"} := "re" * "re" + "im" * "im" in
     `{ "neg"
      ; "conj"
      ; "add"
      ; "sub"
      ; "norm2" } }>.
