From Stdlib Require Import String ZArith.
From shift_reset.core Require Import syntax syntax_notation coerce.

Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope term_scope.

Example Array :=
  <{ let "iter" ("f", "a") :=
       for "i" from 0 upto ({TVBuiltin1 "array_length" "a"} - 1) do
         "f" "a".["i"]
     in
     let "iteri" ("f", "a") :=
       for "i" from 0 upto ({TVBuiltin1 "array_length" "a"} - 1) do
         "f" ("i", "a".["i"])
     in
     let "map" ("f", "a") :=
       let "l" := {TVBuiltin1 "array_length" "a"} in
       let "r" := {TVBuiltin2 "array_make" "l" <{ () }>} in
       let _ :=
         for "i" from 0 upto ("l" - 1) do
           let "x" := "f" "a".["i"] in
           "r".["i"] <- "x"
       in
       "r"
     in
     let "mapi" ("f", "a") :=
       let "l" := {TVBuiltin1 "array_length" "a"} in
       let "r" := {TVBuiltin2 "array_make" "l" <{ () }>} in
       let _ :=
         for "i" from 0 upto ("l" - 1) do
           let "x" := "f" ("i", "a".["i"]) in
           "r".["i"] <- "x"
       in
       "r"
     in
     let "map_inplace" ("f", "a") :=
       for "i" from 0 upto ({TVBuiltin1 "array_length" "a"} - 1) do
         let "x" := "f" "a".["i"] in
         "a".["i"] <- "x"
     in
     let "mapi_inplace" ("f", "a") :=
       for "i" from 0 upto ({TVBuiltin1 "array_length" "a"} - 1) do
         let "x" := "f" ("i", "a".["i"]) in
         "a".["i"] <- "x"
     in
     `{ "iter"
      ; "iteri"
      ; "map"
      ; "mapi"
      ; "map_inplace"
      ; "mapi_inplace" } }>.
