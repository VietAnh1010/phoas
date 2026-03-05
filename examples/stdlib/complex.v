From Stdlib Require Import String.
From shift_reset.core Require Import syntax syntax_notation coerce.

Open Scope string_scope.
Open Scope term_scope.

Example Complex :=
  <{ let "neg" "c" :=
       let `{"re"; "im"} := "c" in
       `{"re" := -"re"; "im" := -"im"}
     in
     let "conj" "c" :=
       let `{"re"; "im"} := "c" in
       `{"re"; "im" := -"im"}
     in
     let "add" "args" :=
       let ("c1", "c2") := "args" in
       let `{"re" := "re1"; "im" := "im1"} := "c1" in
       let `{"re" := "re2"; "im" := "im2"} := "c2" in
       `{"re" := "re1" + "re2"; "im" := "im1" + "im2"}
     in
     let "sub" "args" :=
       let ("c1", "c2") := "args" in
       let `{"re" := "re1"; "im" := "im1"} := "c1" in
       let `{"re" := "re2"; "im" := "im2"} := "c2" in
       `{"re" := "re1" - "re2"; "im" := "im1" - "im2"}
     in
     let "norm2" "c" :=
       let `{"re"; "im"} := "c" in
       "re" * "re" + "im" * "im"
     in
     `{ "neg"
      ; "conj"
      ; "add"
      ; "sub"
      ; "norm2" } }>.
