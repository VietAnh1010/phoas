From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope term_scope.

Example Array :=
  <{ let "iter" "args" :=
       let ("f", "a") := "args" in
       let "l" := {TVBuiltin1 "array_length" "a"} in
       for "i" from 0 upto "l" - 1 do "f" "a".["i"]
     in
     let "iteri" "args" :=
       let ("f", "a") := "args" in
       let "l" := {TVBuiltin1 "array_length" "a"} in
       for "i" from 0 upto "l" - 1 do "f" ("i", "a".["i"])
     in
     let "map" "args" :=
       let ("f", "a") := "args" in
       let "l" := {TVBuiltin1 "array_length" "a"} in
       let "r" := {TVBuiltin2 "array_make" "l" <{ () }>} in
       let _ :=
         for "i" from 0 upto ("l" - 1) do
           let "x" := "f" "a".["i"] in
           "r".["i"] <- "x"
       in
       "r"
     in
     let "map_inplace" "args" :=
       let ("f", "a") := "args" in
       let "l" := {TVBuiltin1 "array_length" "a"} in
       for "i" from 0 upto ("l" - 1) do
         let "x" := "f" "a".["i"] in
         "a".["i"] <- "x"
     in
     let "mapi" "args" :=
       let ("f", "a") := "args" in
       let "l" := {TVBuiltin1 "array_length" "a"} in
       let "r" := {TVBuiltin2 "array_make" "l" <{ () }>} in
       let _ :=
         for "i" from 0 upto ("l" - 1) do
           let "x" := "f" ("i", "a".["i"]) in
           "r".["i"] <- "x"
       in
       "r"
     in
     `{ "iter"
      ; "iteri"
      ; "map"
      ; "map_inplace"
      ; "mapi" } }>.
