import BulksketchBridge.Algebra.ModulusSpec
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.Ring

/-!
Explicit polynomial certificates for the degree-64 Rabin argument. The displayed
polynomials are untrusted certificate data; every identity below is proved by
ordinary ring normalization and characteristic-two lemmas in the Lean kernel.
No decision procedure or generated certificate is assumed correct.
-/

namespace BulksketchBridge.Algebra.Gf64

open Polynomial

private theorem cast_2 : (2 : Polynomial (ZMod 2)) = 0 :=
  (CharP.cast_eq_zero_iff _ 2 2).2 (by decide)

private theorem cast_4 : (4 : Polynomial (ZMod 2)) = 0 :=
  (CharP.cast_eq_zero_iff _ 2 4).2 (by decide)

private theorem cast_6 : (6 : Polynomial (ZMod 2)) = 0 :=
  (CharP.cast_eq_zero_iff _ 2 6).2 (by decide)

private theorem cast_8 : (8 : Polynomial (ZMod 2)) = 0 :=
  (CharP.cast_eq_zero_iff _ 2 8).2 (by decide)

private theorem cast_10 : (10 : Polynomial (ZMod 2)) = 0 :=
  (CharP.cast_eq_zero_iff _ 2 10).2 (by decide)

private theorem cast_12 : (12 : Polynomial (ZMod 2)) = 0 :=
  (CharP.cast_eq_zero_iff _ 2 12).2 (by decide)

private theorem cast_14 : (14 : Polynomial (ZMod 2)) = 0 :=
  (CharP.cast_eq_zero_iff _ 2 14).2 (by decide)

private theorem cast_16 : (16 : Polynomial (ZMod 2)) = 0 :=
  (CharP.cast_eq_zero_iff _ 2 16).2 (by decide)

private theorem cast_18 : (18 : Polynomial (ZMod 2)) = 0 :=
  (CharP.cast_eq_zero_iff _ 2 18).2 (by decide)

noncomputable def remainder0 : Polynomial (ZMod 2) := X

noncomputable def remainder1 : Polynomial (ZMod 2) := X ^ 2

noncomputable def remainder2 : Polynomial (ZMod 2) := X ^ 4

noncomputable def remainder3 : Polynomial (ZMod 2) := X ^ 8

noncomputable def remainder4 : Polynomial (ZMod 2) := X ^ 16

noncomputable def remainder5 : Polynomial (ZMod 2) := X ^ 32

noncomputable def remainder6 : Polynomial (ZMod 2) := X ^ 4 + X ^ 3 + X + 1

noncomputable def remainder7 : Polynomial (ZMod 2) := X ^ 8 + X ^ 6 + X ^ 2 + 1

noncomputable def remainder8 : Polynomial (ZMod 2) := X ^ 16 + X ^ 12 + X ^ 4 + 1

noncomputable def remainder9 : Polynomial (ZMod 2) := X ^ 32 + X ^ 24 + X ^ 8 + 1

noncomputable def remainder10 : Polynomial (ZMod 2) := X ^ 48 + X ^ 16 + X ^ 4 + X ^ 3 + X

noncomputable def remainder11 : Polynomial (ZMod 2) := X ^ 36 + X ^ 35 + X ^ 33 + X ^ 8 + X ^ 6 + X ^ 2

noncomputable def remainder12 : Polynomial (ZMod 2) := X ^ 16 + X ^ 11 + X ^ 10 + X ^ 8 + X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2

noncomputable def remainder13 : Polynomial (ZMod 2) := X ^ 32 + X ^ 22 + X ^ 20 + X ^ 16 + X ^ 14 + X ^ 10 + X ^ 8 + X ^ 6 + X ^ 4

noncomputable def remainder14 : Polynomial (ZMod 2) := X ^ 44 + X ^ 40 + X ^ 32 + X ^ 28 + X ^ 20 + X ^ 16 + X ^ 12 + X ^ 8 + X ^ 4 + X ^ 3 + X + 1

noncomputable def remainder15 : Polynomial (ZMod 2) := X ^ 56 + X ^ 40 + X ^ 32 + X ^ 28 + X ^ 27 + X ^ 25 + X ^ 20 + X ^ 19 + X ^ 17 + X ^ 8 + X ^ 6 + X ^ 4 + X ^ 3 + X ^ 2 + X

noncomputable def remainder16 : Polynomial (ZMod 2) := X ^ 56 + X ^ 54 + X ^ 52 + X ^ 51 + X ^ 50 + X ^ 49 + X ^ 48 + X ^ 40 + X ^ 38 + X ^ 34 + X ^ 20 + X ^ 19 + X ^ 17 + X ^ 12 + X ^ 8 + X ^ 6 + X ^ 3 + X ^ 2 + X + 1

noncomputable def remainder17 : Polynomial (ZMod 2) := X ^ 52 + X ^ 51 + X ^ 49 + X ^ 47 + X ^ 45 + X ^ 43 + X ^ 42 + X ^ 40 + X ^ 38 + X ^ 33 + X ^ 32 + X ^ 24 + X ^ 20 + X ^ 19 + X ^ 17 + X ^ 16 + X ^ 15 + X ^ 13 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 2 + 1

noncomputable def remainder18 : Polynomial (ZMod 2) := X ^ 48 + X ^ 44 + X ^ 43 + X ^ 42 + X ^ 39 + X ^ 38 + X ^ 37 + X ^ 35 + X ^ 34 + X ^ 33 + X ^ 32 + X ^ 31 + X ^ 30 + X ^ 29 + X ^ 27 + X ^ 26 + X ^ 25 + X ^ 24 + X ^ 22 + X ^ 21 + X ^ 19 + X ^ 17 + X ^ 16 + X ^ 15 + X ^ 14 + X ^ 13 + X ^ 10 + X ^ 6 + X ^ 5 + X ^ 2 + X

noncomputable def remainder19 : Polynomial (ZMod 2) := X ^ 62 + X ^ 60 + X ^ 58 + X ^ 54 + X ^ 52 + X ^ 50 + X ^ 48 + X ^ 44 + X ^ 42 + X ^ 38 + X ^ 36 + X ^ 35 + X ^ 34 + X ^ 33 + X ^ 30 + X ^ 27 + X ^ 22 + X ^ 21 + X ^ 18 + X ^ 17 + X ^ 16 + X ^ 11 + X ^ 10 + X ^ 9 + X ^ 8 + X ^ 4 + X + 1

noncomputable def remainder20 : Polynomial (ZMod 2) := X ^ 63 + X ^ 61 + X ^ 60 + X ^ 59 + X ^ 57 + X ^ 55 + X ^ 54 + X ^ 53 + X ^ 52 + X ^ 48 + X ^ 47 + X ^ 45 + X ^ 44 + X ^ 43 + X ^ 42 + X ^ 41 + X ^ 39 + X ^ 37 + X ^ 36 + X ^ 35 + X ^ 34 + X ^ 33 + X ^ 28 + X ^ 27 + X ^ 25 + X ^ 23 + X ^ 22 + X ^ 21 + X ^ 18 + X ^ 15 + X ^ 13 + X ^ 11 + X ^ 10 + X ^ 8 + X

noncomputable def remainder21 : Polynomial (ZMod 2) := X ^ 63 + X ^ 61 + X ^ 60 + X ^ 55 + X ^ 54 + X ^ 53 + X ^ 51 + X ^ 50 + X ^ 49 + X ^ 48 + X ^ 46 + X ^ 44 + X ^ 41 + X ^ 40 + X ^ 35 + X ^ 34 + X ^ 32 + X ^ 31 + X ^ 30 + X ^ 29 + X ^ 28 + X ^ 26 + X ^ 22 + X ^ 19 + X ^ 17 + X ^ 16 + X ^ 15 + X ^ 13 + X ^ 12 + X ^ 6 + X

noncomputable def remainder22 : Polynomial (ZMod 2) := X ^ 63 + X ^ 62 + X ^ 61 + X ^ 57 + X ^ 52 + X ^ 50 + X ^ 49 + X ^ 48 + X ^ 43 + X ^ 41 + X ^ 40 + X ^ 38 + X ^ 33 + X ^ 32 + X ^ 31 + X ^ 30 + X ^ 29 + X ^ 27 + X ^ 26 + X ^ 25 + X ^ 22 + X ^ 21 + X ^ 20 + X ^ 18 + X ^ 17 + X ^ 16 + X ^ 12 + X ^ 10 + X ^ 9 + X ^ 8 + X ^ 5 + X ^ 4 + X ^ 2 + 1

noncomputable def remainder23 : Polynomial (ZMod 2) := X ^ 62 + X ^ 59 + X ^ 53 + X ^ 52 + X ^ 51 + X ^ 43 + X ^ 42 + X ^ 41 + X ^ 40 + X ^ 39 + X ^ 38 + X ^ 36 + X ^ 33 + X ^ 26 + X ^ 25 + X ^ 24 + X ^ 23 + X ^ 21 + X ^ 17 + X ^ 16 + X ^ 15 + X ^ 13 + X ^ 12 + X ^ 10 + X ^ 8 + X ^ 5 + X ^ 2 + X + 1

noncomputable def remainder24 : Polynomial (ZMod 2) := X ^ 63 + X ^ 61 + X ^ 60 + X ^ 58 + X ^ 57 + X ^ 55 + X ^ 54 + X ^ 52 + X ^ 50 + X ^ 48 + X ^ 45 + X ^ 44 + X ^ 42 + X ^ 40 + X ^ 39 + X ^ 38 + X ^ 34 + X ^ 32 + X ^ 30 + X ^ 25 + X ^ 20 + X ^ 16 + X ^ 14 + X ^ 13 + X ^ 11 + X ^ 10 + X ^ 9 + X ^ 8 + X ^ 6 + X ^ 5 + X

noncomputable def remainder25 : Polynomial (ZMod 2) := X ^ 63 + X ^ 61 + X ^ 58 + X ^ 57 + X ^ 55 + X ^ 54 + X ^ 52 + X ^ 51 + X ^ 50 + X ^ 49 + X ^ 48 + X ^ 46 + X ^ 45 + X ^ 43 + X ^ 41 + X ^ 40 + X ^ 39 + X ^ 37 + X ^ 35 + X ^ 33 + X ^ 30 + X ^ 29 + X ^ 25 + X ^ 23 + X ^ 22 + X ^ 21 + X ^ 20 + X ^ 19 + X ^ 16 + X ^ 14 + X ^ 13 + X ^ 10 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2 + 1

noncomputable def remainder26 : Polynomial (ZMod 2) := X ^ 63 + X ^ 61 + X ^ 60 + X ^ 59 + X ^ 56 + X ^ 55 + X ^ 54 + X ^ 52 + X ^ 51 + X ^ 50 + X ^ 49 + X ^ 48 + X ^ 45 + X ^ 44 + X ^ 43 + X ^ 40 + X ^ 38 + X ^ 34 + X ^ 33 + X ^ 32 + X ^ 31 + X ^ 30 + X ^ 27 + X ^ 26 + X ^ 25 + X ^ 23 + X ^ 21 + X ^ 15 + X ^ 14 + X ^ 13 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 2 + X + 1

noncomputable def remainder27 : Polynomial (ZMod 2) := X ^ 63 + X ^ 62 + X ^ 61 + X ^ 56 + X ^ 55 + X ^ 51 + X ^ 45 + X ^ 43 + X ^ 34 + X ^ 33 + X ^ 32 + X ^ 29 + X ^ 26 + X ^ 23 + X ^ 19 + X ^ 18 + X ^ 17 + X ^ 16 + X ^ 15 + X ^ 14 + X ^ 13 + X ^ 10 + X ^ 8 + X ^ 7 + X ^ 3

noncomputable def remainder28 : Polynomial (ZMod 2) := X ^ 60 + X ^ 59 + X ^ 51 + X ^ 50 + X ^ 48 + X ^ 47 + X ^ 42 + X ^ 41 + X ^ 39 + X ^ 36 + X ^ 34 + X ^ 32 + X ^ 29 + X ^ 28 + X ^ 27 + X ^ 26 + X ^ 25 + X ^ 23 + X ^ 22 + X ^ 20 + X ^ 16 + X ^ 14 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 2 + X

noncomputable def remainder29 : Polynomial (ZMod 2) := X ^ 60 + X ^ 59 + X ^ 55 + X ^ 52 + X ^ 50 + X ^ 46 + X ^ 44 + X ^ 42 + X ^ 41 + X ^ 38 + X ^ 37 + X ^ 35 + X ^ 34 + X ^ 31 + X ^ 30 + X ^ 28 + X ^ 24 + X ^ 23 + X ^ 22 + X ^ 20 + X ^ 19 + X ^ 17 + X ^ 16 + X ^ 15 + X ^ 11 + X ^ 9 + X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1

noncomputable def remainder30 : Polynomial (ZMod 2) := X ^ 62 + X ^ 59 + X ^ 58 + X ^ 55 + X ^ 54 + X ^ 50 + X ^ 49 + X ^ 48 + X ^ 47 + X ^ 43 + X ^ 41 + X ^ 40 + X ^ 39 + X ^ 38 + X ^ 37 + X ^ 36 + X ^ 34 + X ^ 31 + X ^ 30 + X ^ 29 + X ^ 27 + X ^ 25 + X ^ 23 + X ^ 20 + X ^ 19 + X ^ 16 + X ^ 15 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 9 + X ^ 5 + X ^ 2 + 1

noncomputable def remainder31 : Polynomial (ZMod 2) := X ^ 63 + X ^ 62 + X ^ 61 + X ^ 57 + X ^ 56 + X ^ 53 + X ^ 52 + X ^ 49 + X ^ 48 + X ^ 45 + X ^ 44 + X ^ 39 + X ^ 31 + X ^ 26 + X ^ 25 + X ^ 24 + X ^ 23 + X ^ 22 + X ^ 21 + X ^ 18 + X ^ 9 + X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + X

noncomputable def remainder32 : Polynomial (ZMod 2) := X ^ 62 + X ^ 60 + X ^ 59 + X ^ 58 + X ^ 54 + X ^ 53 + X ^ 49 + X ^ 45 + X ^ 41 + X ^ 40 + X ^ 38 + X ^ 37 + X ^ 34 + X ^ 33 + X ^ 32 + X ^ 30 + X ^ 29 + X ^ 28 + X ^ 26 + X ^ 25 + X ^ 24 + X ^ 17 + X ^ 15 + X ^ 10 + X ^ 8 + X ^ 2 + 1

noncomputable def remainder33 : Polynomial (ZMod 2) := X ^ 63 + X ^ 61 + X ^ 60 + X ^ 59 + X ^ 56 + X ^ 54 + X ^ 53 + X ^ 50 + X ^ 47 + X ^ 46 + X ^ 44 + X ^ 43 + X ^ 42 + X ^ 38 + X ^ 37 + X ^ 35 + X ^ 29 + X ^ 27 + X ^ 26 + X ^ 22 + X ^ 21 + X ^ 18 + X ^ 17 + X ^ 16 + X ^ 15 + X ^ 14 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 3 + X ^ 2 + 1

noncomputable def remainder34 : Polynomial (ZMod 2) := X ^ 63 + X ^ 61 + X ^ 60 + X ^ 58 + X ^ 56 + X ^ 55 + X ^ 51 + X ^ 49 + X ^ 47 + X ^ 46 + X ^ 43 + X ^ 40 + X ^ 39 + X ^ 37 + X ^ 33 + X ^ 29 + X ^ 28 + X ^ 27 + X ^ 26 + X ^ 24 + X ^ 21 + X ^ 15 + X ^ 11 + X ^ 9 + X ^ 7 + X ^ 6 + X ^ 3 + X + 1

noncomputable def remainder35 : Polynomial (ZMod 2) := X ^ 63 + X ^ 61 + X ^ 60 + X ^ 57 + X ^ 56 + X ^ 55 + X ^ 54 + X ^ 53 + X ^ 52 + X ^ 51 + X ^ 50 + X ^ 47 + X ^ 46 + X ^ 41 + X ^ 39 + X ^ 37 + X ^ 35 + X ^ 33 + X ^ 32 + X ^ 29 + X ^ 28 + X ^ 26 + X ^ 25 + X ^ 23 + X ^ 20 + X ^ 19 + X ^ 16 + X ^ 15 + X ^ 14 + X ^ 13 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 6 + X ^ 5 + X ^ 4 + X + 1

noncomputable def remainder36 : Polynomial (ZMod 2) := X ^ 63 + X ^ 61 + X ^ 60 + X ^ 57 + X ^ 54 + X ^ 53 + X ^ 50 + X ^ 46 + X ^ 40 + X ^ 37 + X ^ 36 + X ^ 34 + X ^ 33 + X ^ 29 + X ^ 26 + X ^ 24 + X ^ 21 + X ^ 20 + X ^ 19 + X ^ 17 + X ^ 15 + X ^ 13 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3

noncomputable def remainder37 : Polynomial (ZMod 2) := X ^ 63 + X ^ 61 + X ^ 60 + X ^ 57 + X ^ 56 + X ^ 54 + X ^ 53 + X ^ 52 + X ^ 51 + X ^ 50 + X ^ 47 + X ^ 46 + X ^ 44 + X ^ 43 + X ^ 39 + X ^ 38 + X ^ 37 + X ^ 36 + X ^ 34 + X ^ 32 + X ^ 31 + X ^ 30 + X ^ 29 + X ^ 28 + X ^ 26 + X ^ 24 + X ^ 22 + X ^ 19 + X ^ 18 + X ^ 17 + X ^ 13 + X ^ 9 + X ^ 7 + X ^ 6 + X ^ 2 + X

noncomputable def remainder38 : Polynomial (ZMod 2) := X ^ 63 + X ^ 62 + X ^ 61 + X ^ 57 + X ^ 54 + X ^ 53 + X ^ 50 + X ^ 49 + X ^ 48 + X ^ 47 + X ^ 46 + X ^ 44 + X ^ 37 + X ^ 33 + X ^ 32 + X ^ 30 + X ^ 29 + X ^ 27 + X ^ 24 + X ^ 23 + X ^ 22 + X ^ 17 + X ^ 16 + X ^ 14 + X ^ 12 + X ^ 10 + X ^ 9 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 2 + 1

noncomputable def remainder39 : Polynomial (ZMod 2) := X ^ 59 + X ^ 53 + X ^ 51 + X ^ 50 + X ^ 47 + X ^ 43 + X ^ 42 + X ^ 40 + X ^ 39 + X ^ 38 + X ^ 34 + X ^ 32 + X ^ 30 + X ^ 29 + X ^ 28 + X ^ 27 + X ^ 25 + X ^ 20 + X ^ 18 + X ^ 13 + X ^ 12 + X ^ 11 + X ^ 5 + X ^ 2 + X + 1

noncomputable def remainder40 : Polynomial (ZMod 2) := X ^ 60 + X ^ 57 + X ^ 56 + X ^ 55 + X ^ 50 + X ^ 46 + X ^ 45 + X ^ 43 + X ^ 41 + X ^ 38 + X ^ 37 + X ^ 34 + X ^ 33 + X ^ 31 + X ^ 30 + X ^ 25 + X ^ 21 + X ^ 19 + X ^ 18 + X ^ 14 + X ^ 13 + X ^ 12 + X ^ 10 + X ^ 8 + X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X

noncomputable def remainder41 : Polynomial (ZMod 2) := X ^ 62 + X ^ 59 + X ^ 57 + X ^ 56 + X ^ 54 + X ^ 53 + X ^ 52 + X ^ 50 + X ^ 48 + X ^ 47 + X ^ 46 + X ^ 42 + X ^ 40 + X ^ 39 + X ^ 38 + X ^ 37 + X ^ 32 + X ^ 31 + X ^ 30 + X ^ 27 + X ^ 26 + X ^ 25 + X ^ 24 + X ^ 23 + X ^ 21 + X ^ 20 + X ^ 19 + X ^ 18 + X ^ 15 + X ^ 12 + X ^ 11 + X ^ 7 + X ^ 3

noncomputable def remainder42 : Polynomial (ZMod 2) := X ^ 63 + X ^ 62 + X ^ 61 + X ^ 58 + X ^ 57 + X ^ 55 + X ^ 54 + X ^ 53 + X ^ 49 + X ^ 48 + X ^ 47 + X ^ 41 + X ^ 40 + X ^ 39 + X ^ 38 + X ^ 37 + X ^ 36 + X ^ 35 + X ^ 34 + X ^ 29 + X ^ 28 + X ^ 23 + X ^ 22 + X ^ 21 + X ^ 19 + X ^ 18 + X ^ 14 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 6

noncomputable def remainder43 : Polynomial (ZMod 2) := X ^ 60 + X ^ 59 + X ^ 55 + X ^ 54 + X ^ 52 + X ^ 51 + X ^ 49 + X ^ 48 + X ^ 46 + X ^ 43 + X ^ 37 + X ^ 32 + X ^ 31 + X ^ 30 + X ^ 28 + X ^ 24 + X ^ 21 + X ^ 12 + X ^ 5 + X ^ 4 + 1

noncomputable def remainder44 : Polynomial (ZMod 2) := X ^ 62 + X ^ 59 + X ^ 58 + X ^ 55 + X ^ 54 + X ^ 50 + X ^ 49 + X ^ 46 + X ^ 45 + X ^ 43 + X ^ 40 + X ^ 39 + X ^ 37 + X ^ 36 + X ^ 34 + X ^ 33 + X ^ 31 + X ^ 29 + X ^ 28 + X ^ 26 + X ^ 25 + X ^ 24 + X ^ 23 + X ^ 22 + X ^ 14 + X ^ 13 + X ^ 11 + X ^ 8 + X ^ 4 + X ^ 3 + X

noncomputable def remainder45 : Polynomial (ZMod 2) := X ^ 63 + X ^ 62 + X ^ 61 + X ^ 60 + X ^ 57 + X ^ 54 + X ^ 53 + X ^ 49 + X ^ 45 + X ^ 40 + X ^ 39 + X ^ 38 + X ^ 36 + X ^ 35 + X ^ 34 + X ^ 32 + X ^ 31 + X ^ 30 + X ^ 27 + X ^ 26 + X ^ 25 + X ^ 23 + X ^ 20 + X ^ 19 + X ^ 18 + X ^ 15 + X ^ 13 + X ^ 12 + X ^ 10 + X ^ 9 + X ^ 8 + X ^ 7 + X + 1

noncomputable def remainder46 : Polynomial (ZMod 2) := X ^ 62 + X ^ 60 + X ^ 58 + X ^ 57 + X ^ 56 + X ^ 53 + X ^ 52 + X ^ 51 + X ^ 48 + X ^ 47 + X ^ 44 + X ^ 43 + X ^ 42 + X ^ 40 + X ^ 37 + X ^ 36 + X ^ 35 + X ^ 34 + X ^ 29 + X ^ 27 + X ^ 24 + X ^ 19 + X ^ 16 + X ^ 13 + X ^ 11 + X ^ 10 + X ^ 5 + X ^ 3 + X ^ 2 + X + 1

noncomputable def remainder47 : Polynomial (ZMod 2) := X ^ 63 + X ^ 61 + X ^ 59 + X ^ 58 + X ^ 57 + X ^ 55 + X ^ 50 + X ^ 49 + X ^ 46 + X ^ 45 + X ^ 44 + X ^ 40 + X ^ 39 + X ^ 36 + X ^ 35 + X ^ 34 + X ^ 31 + X ^ 30 + X ^ 28 + X ^ 27 + X ^ 21 + X ^ 20 + X ^ 19 + X ^ 17 + X ^ 16 + X ^ 14 + X ^ 13 + X ^ 12 + X ^ 10 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X

noncomputable def remainder48 : Polynomial (ZMod 2) := X ^ 63 + X ^ 62 + X ^ 61 + X ^ 60 + X ^ 59 + X ^ 57 + X ^ 54 + X ^ 52 + X ^ 51 + X ^ 49 + X ^ 47 + X ^ 46 + X ^ 42 + X ^ 39 + X ^ 36 + X ^ 35 + X ^ 31 + X ^ 30 + X ^ 28 + X ^ 25 + X ^ 19 + X ^ 18 + X ^ 16 + X ^ 15 + X ^ 14 + X ^ 12 + X ^ 11 + X ^ 8 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X

noncomputable def remainder49 : Polynomial (ZMod 2) := X ^ 62 + X ^ 60 + X ^ 55 + X ^ 53 + X ^ 51 + X ^ 48 + X ^ 47 + X ^ 45 + X ^ 43 + X ^ 42 + X ^ 40 + X ^ 39 + X ^ 38 + X ^ 37 + X ^ 36 + X ^ 35 + X ^ 33 + X ^ 29 + X ^ 23 + X ^ 22 + X ^ 21 + X ^ 20 + X ^ 18 + X ^ 17 + X ^ 16 + X ^ 15 + X ^ 14 + X ^ 11 + X ^ 7 + X ^ 6 + X ^ 4 + X ^ 2 + 1

noncomputable def remainder50 : Polynomial (ZMod 2) := X ^ 63 + X ^ 61 + X ^ 59 + X ^ 58 + X ^ 57 + X ^ 56 + X ^ 50 + X ^ 49 + X ^ 47 + X ^ 46 + X ^ 45 + X ^ 44 + X ^ 43 + X ^ 42 + X ^ 41 + X ^ 40 + X ^ 39 + X ^ 38 + X ^ 35 + X ^ 31 + X ^ 30 + X ^ 29 + X ^ 28 + X ^ 27 + X ^ 25 + X ^ 24 + X ^ 21 + X ^ 19 + X ^ 18 + X ^ 14 + X ^ 12 + X ^ 7 + X ^ 5 + X ^ 2 + X

noncomputable def remainder51 : Polynomial (ZMod 2) := X ^ 63 + X ^ 62 + X ^ 61 + X ^ 60 + X ^ 59 + X ^ 58 + X ^ 57 + X ^ 54 + X ^ 49 + X ^ 42 + X ^ 40 + X ^ 39 + X ^ 35 + X ^ 33 + X ^ 32 + X ^ 28 + X ^ 24 + X ^ 13 + X ^ 12 + X ^ 9 + X ^ 7 + X ^ 3 + X ^ 2 + X

noncomputable def remainder52 : Polynomial (ZMod 2) := X ^ 56 + X ^ 52 + X ^ 51 + X ^ 50 + X ^ 47 + X ^ 45 + X ^ 44 + X ^ 38 + X ^ 37 + X ^ 35 + X ^ 34 + X ^ 26 + X ^ 23 + X ^ 21 + X ^ 19 + X ^ 16 + X ^ 15 + X ^ 10 + X ^ 9 + X ^ 7 + X ^ 5 + X

noncomputable def remainder53 : Polynomial (ZMod 2) := X ^ 51 + X ^ 49 + X ^ 48 + X ^ 46 + X ^ 44 + X ^ 43 + X ^ 37 + X ^ 36 + X ^ 34 + X ^ 33 + X ^ 32 + X ^ 31 + X ^ 30 + X ^ 29 + X ^ 28 + X ^ 26 + X ^ 25 + X ^ 24 + X ^ 20 + X ^ 18 + X ^ 16 + X ^ 15 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 9 + X ^ 8 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 2

noncomputable def remainder54 : Polynomial (ZMod 2) := X ^ 62 + X ^ 60 + X ^ 58 + X ^ 56 + X ^ 52 + X ^ 50 + X ^ 48 + X ^ 42 + X ^ 41 + X ^ 40 + X ^ 39 + X ^ 37 + X ^ 34 + X ^ 33 + X ^ 32 + X ^ 31 + X ^ 30 + X ^ 29 + X ^ 27 + X ^ 26 + X ^ 23 + X ^ 20 + X ^ 18 + X ^ 16 + X ^ 14 + X ^ 13 + X ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 4 + X ^ 2 + X + 1

noncomputable def remainder55 : Polynomial (ZMod 2) := X ^ 63 + X ^ 62 + X ^ 61 + X ^ 60 + X ^ 59 + X ^ 58 + X ^ 57 + X ^ 55 + X ^ 54 + X ^ 53 + X ^ 52 + X ^ 51 + X ^ 49 + X ^ 48 + X ^ 46 + X ^ 44 + X ^ 43 + X ^ 41 + X ^ 40 + X ^ 39 + X ^ 37 + X ^ 36 + X ^ 35 + X ^ 33 + X ^ 28 + X ^ 26 + X ^ 24 + X ^ 23 + X ^ 22 + X ^ 18 + X ^ 15 + X ^ 14 + X ^ 13 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 7 + X ^ 6 + X ^ 3 + 1

noncomputable def remainder56 : Polynomial (ZMod 2) := X ^ 56 + X ^ 51 + X ^ 49 + X ^ 46 + X ^ 44 + X ^ 40 + X ^ 39 + X ^ 37 + X ^ 34 + X ^ 33 + X ^ 31 + X ^ 30 + X ^ 29 + X ^ 28 + X ^ 27 + X ^ 23 + X ^ 22 + X ^ 21 + X ^ 16 + X ^ 15 + X ^ 14 + X ^ 13 + X ^ 8 + X ^ 7 + X ^ 5 + X ^ 3 + X ^ 2

noncomputable def remainder57 : Polynomial (ZMod 2) := X ^ 62 + X ^ 60 + X ^ 58 + X ^ 56 + X ^ 54 + X ^ 52 + X ^ 51 + X ^ 49 + X ^ 48 + X ^ 46 + X ^ 44 + X ^ 41 + X ^ 39 + X ^ 37 + X ^ 35 + X ^ 34 + X ^ 31 + X ^ 30 + X ^ 29 + X ^ 28 + X ^ 27 + X ^ 26 + X ^ 25 + X ^ 24 + X ^ 20 + X ^ 19 + X ^ 18 + X ^ 15 + X ^ 14 + X ^ 13 + X ^ 11 + X ^ 8 + X ^ 7 + X ^ 3 + X ^ 2

noncomputable def remainder58 : Polynomial (ZMod 2) := X ^ 63 + X ^ 62 + X ^ 61 + X ^ 60 + X ^ 59 + X ^ 58 + X ^ 57 + X ^ 56 + X ^ 55 + X ^ 54 + X ^ 53 + X ^ 52 + X ^ 51 + X ^ 50 + X ^ 49 + X ^ 48 + X ^ 47 + X ^ 45 + X ^ 43 + X ^ 42 + X ^ 39 + X ^ 38 + X ^ 37 + X ^ 34 + X ^ 33 + X ^ 31 + X ^ 30 + X ^ 29 + X ^ 28 + X ^ 27 + X ^ 26 + X ^ 25 + X ^ 24 + X ^ 21 + X ^ 19 + X ^ 17 + X ^ 16 + X ^ 15 + X ^ 14 + X ^ 13 + X ^ 11 + X ^ 9 + X ^ 8 + X ^ 5 + X ^ 4 + X ^ 3 + X + 1

noncomputable def remainder59 : Polynomial (ZMod 2) := X ^ 62 + X ^ 60 + X ^ 58 + X ^ 56 + X ^ 54 + X ^ 52 + X ^ 50 + X ^ 48 + X ^ 42 + X ^ 38 + X ^ 34 + X ^ 31 + X ^ 30 + X ^ 29 + X ^ 28 + X ^ 27 + X ^ 26 + X ^ 25 + X ^ 24 + X ^ 21 + X ^ 20 + X ^ 17 + X ^ 12 + X ^ 11 + X ^ 7 + X ^ 6 + X ^ 4 + X ^ 3

noncomputable def remainder60 : Polynomial (ZMod 2) := X ^ 63 + X ^ 62 + X ^ 61 + X ^ 60 + X ^ 59 + X ^ 58 + X ^ 57 + X ^ 56 + X ^ 55 + X ^ 54 + X ^ 53 + X ^ 52 + X ^ 51 + X ^ 50 + X ^ 49 + X ^ 48 + X ^ 47 + X ^ 45 + X ^ 43 + X ^ 42 + X ^ 41 + X ^ 40 + X ^ 39 + X ^ 37 + X ^ 35 + X ^ 34 + X ^ 33 + X ^ 32 + X ^ 23 + X ^ 22 + X ^ 21 + X ^ 20 + X ^ 16 + X ^ 15 + X ^ 14 + X ^ 13 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3 + X + 1

noncomputable def remainder61 : Polynomial (ZMod 2) := X ^ 46 + X ^ 44 + X ^ 42 + X ^ 40 + X ^ 31 + X ^ 30 + X ^ 29 + X ^ 28 + X ^ 27 + X ^ 26 + X ^ 25 + X ^ 24 + X ^ 16 + X ^ 15 + X ^ 14 + X ^ 13 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 9 + X ^ 8 + X + 1

noncomputable def remainder62 : Polynomial (ZMod 2) := X ^ 62 + X ^ 60 + X ^ 58 + X ^ 56 + X ^ 54 + X ^ 52 + X ^ 50 + X ^ 48 + X ^ 31 + X ^ 30 + X ^ 29 + X ^ 28 + X ^ 27 + X ^ 26 + X ^ 25 + X ^ 24 + X ^ 23 + X ^ 22 + X ^ 21 + X ^ 20 + X ^ 19 + X ^ 18 + X ^ 17 + X ^ 2 + 1

noncomputable def remainder63 : Polynomial (ZMod 2) := X ^ 63 + X ^ 62 + X ^ 61 + X ^ 60 + X ^ 59 + X ^ 58 + X ^ 57 + X ^ 56 + X ^ 55 + X ^ 54 + X ^ 53 + X ^ 52 + X ^ 51 + X ^ 50 + X ^ 49 + X ^ 48 + X ^ 47 + X ^ 46 + X ^ 45 + X ^ 44 + X ^ 43 + X ^ 42 + X ^ 41 + X ^ 40 + X ^ 39 + X ^ 38 + X ^ 37 + X ^ 36 + X ^ 35 + X ^ 34 + X ^ 33 + X ^ 32 + X ^ 3 + X

noncomputable def remainder64 : Polynomial (ZMod 2) := X

theorem square_certificate_0 :
    remainder0 ^ 2 + modulus * (0) + remainder1 = 0 := by
  unfold remainder0 remainder1 modulus
  ring_nf
  simp [cast_2]

theorem square_certificate_1 :
    remainder1 ^ 2 + modulus * (0) + remainder2 = 0 := by
  unfold remainder1 remainder2 modulus
  ring_nf
  simp [cast_2]

theorem square_certificate_2 :
    remainder2 ^ 2 + modulus * (0) + remainder3 = 0 := by
  unfold remainder2 remainder3 modulus
  ring_nf
  simp [cast_2]

theorem square_certificate_3 :
    remainder3 ^ 2 + modulus * (0) + remainder4 = 0 := by
  unfold remainder3 remainder4 modulus
  ring_nf
  simp [cast_2]

theorem square_certificate_4 :
    remainder4 ^ 2 + modulus * (0) + remainder5 = 0 := by
  unfold remainder4 remainder5 modulus
  ring_nf
  simp [cast_2]

theorem square_certificate_5 :
    remainder5 ^ 2 + modulus * (1) + remainder6 = 0 := by
  unfold remainder5 remainder6 modulus
  ring_nf
  simp [cast_2]

theorem square_certificate_6 :
    remainder6 ^ 2 + modulus * (0) + remainder7 = 0 := by
  unfold remainder6 remainder7 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2]

theorem square_certificate_7 :
    remainder7 ^ 2 + modulus * (0) + remainder8 = 0 := by
  unfold remainder7 remainder8 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2]

theorem square_certificate_8 :
    remainder8 ^ 2 + modulus * (0) + remainder9 = 0 := by
  unfold remainder8 remainder9 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2]

theorem square_certificate_9 :
    remainder9 ^ 2 + modulus * (1) + remainder10 = 0 := by
  unfold remainder9 remainder10 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2]

theorem square_certificate_10 :
    remainder10 ^ 2 + modulus * (X ^ 32) + remainder11 = 0 := by
  unfold remainder10 remainder11 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2]

theorem square_certificate_11 :
    remainder11 ^ 2 + modulus * (X ^ 8 + X ^ 6 + X ^ 2) + remainder12 = 0 := by
  unfold remainder11 remainder12 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2]

theorem square_certificate_12 :
    remainder12 ^ 2 + modulus * (0) + remainder13 = 0 := by
  unfold remainder12 remainder13 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2]

theorem square_certificate_13 :
    remainder13 ^ 2 + modulus * (1) + remainder14 = 0 := by
  unfold remainder13 remainder14 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2]

theorem square_certificate_14 :
    remainder14 ^ 2 + modulus * (X ^ 24 + X ^ 16 + 1) + remainder15 = 0 := by
  unfold remainder14 remainder15 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2]

theorem square_certificate_15 :
    remainder15 ^ 2 + modulus * (X ^ 48 + X ^ 16 + 1) + remainder16 = 0 := by
  unfold remainder15 remainder16 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2]

theorem square_certificate_16 :
    remainder16 ^ 2 + modulus * (X ^ 48 + X ^ 44 + X ^ 40 + X ^ 38 + X ^ 36 + X ^ 34 + X ^ 32 + X ^ 16 + X ^ 12 + X ^ 4) + remainder17 = 0 := by
  unfold remainder16 remainder17 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_17 :
    remainder17 ^ 2 + modulus * (X ^ 40 + X ^ 38 + X ^ 34 + X ^ 30 + X ^ 26 + X ^ 22 + X ^ 20 + X ^ 16 + X ^ 12 + X ^ 2 + 1) + remainder18 = 0 := by
  unfold remainder17 remainder18 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_18 :
    remainder18 ^ 2 + modulus * (X ^ 32 + X ^ 24 + X ^ 22 + X ^ 20 + X ^ 14 + X ^ 12 + X ^ 10 + X ^ 6 + X ^ 4 + X ^ 2 + 1) + remainder19 = 0 := by
  unfold remainder18 remainder19 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_19 :
    remainder19 ^ 2 + modulus * (X ^ 60 + X ^ 56 + X ^ 52 + X ^ 44 + X ^ 40 + X ^ 36 + X ^ 32 + X ^ 24 + X ^ 20 + X ^ 12 + X ^ 8 + X ^ 6 + X ^ 4 + X ^ 2 + 1) + remainder20 = 0 := by
  unfold remainder19 remainder20 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_20 :
    remainder20 ^ 2 + modulus * (X ^ 62 + X ^ 58 + X ^ 56 + X ^ 54 + X ^ 50 + X ^ 46 + X ^ 44 + X ^ 42 + X ^ 40 + X ^ 32 + X ^ 30 + X ^ 26 + X ^ 24 + X ^ 22 + X ^ 20 + X ^ 18 + X ^ 14 + X ^ 10 + X ^ 8 + X ^ 6 + X ^ 4 + X) + remainder21 = 0 := by
  unfold remainder20 remainder21 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_21 :
    remainder21 ^ 2 + modulus * (X ^ 62 + X ^ 58 + X ^ 56 + X ^ 46 + X ^ 44 + X ^ 42 + X ^ 38 + X ^ 36 + X ^ 34 + X ^ 32 + X ^ 28 + X ^ 24 + X ^ 18 + X ^ 16 + X ^ 6 + X ^ 4 + X ^ 2 + X + 1) + remainder22 = 0 := by
  unfold remainder21 remainder22 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_22 :
    remainder22 ^ 2 + modulus * (X ^ 62 + X ^ 60 + X ^ 58 + X ^ 50 + X ^ 40 + X ^ 36 + X ^ 34 + X ^ 32 + X ^ 22 + X ^ 18 + X ^ 16 + X ^ 12 + X) + remainder23 = 0 := by
  unfold remainder22 remainder23 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_23 :
    remainder23 ^ 2 + modulus * (X ^ 60 + X ^ 54 + X ^ 42 + X ^ 40 + X ^ 38 + X ^ 22 + X ^ 20 + X ^ 18 + X ^ 16 + X ^ 14 + X ^ 12 + X ^ 8 + X ^ 2 + 1) + remainder24 = 0 := by
  unfold remainder23 remainder24 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_24 :
    remainder24 ^ 2 + modulus * (X ^ 62 + X ^ 58 + X ^ 56 + X ^ 52 + X ^ 50 + X ^ 46 + X ^ 44 + X ^ 40 + X ^ 36 + X ^ 32 + X ^ 26 + X ^ 24 + X ^ 20 + X ^ 16 + X ^ 14 + X ^ 12 + X ^ 4 + X ^ 2 + X + 1) + remainder25 = 0 := by
  unfold remainder24 remainder25 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_25 :
    remainder25 ^ 2 + modulus * (X ^ 62 + X ^ 58 + X ^ 52 + X ^ 50 + X ^ 46 + X ^ 44 + X ^ 40 + X ^ 38 + X ^ 36 + X ^ 34 + X ^ 32 + X ^ 28 + X ^ 26 + X ^ 22 + X ^ 18 + X ^ 16 + X ^ 14 + X ^ 10 + X ^ 6 + X) + remainder26 = 0 := by
  unfold remainder25 remainder26 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_26 :
    remainder26 ^ 2 + modulus * (X ^ 62 + X ^ 58 + X ^ 56 + X ^ 54 + X ^ 48 + X ^ 46 + X ^ 44 + X ^ 40 + X ^ 38 + X ^ 36 + X ^ 34 + X ^ 32 + X ^ 26 + X ^ 24 + X ^ 22 + X ^ 16 + X ^ 12 + X ^ 4 + X + 1) + remainder27 = 0 := by
  unfold remainder26 remainder27 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_27 :
    remainder27 ^ 2 + modulus * (X ^ 62 + X ^ 60 + X ^ 58 + X ^ 48 + X ^ 46 + X ^ 38 + X ^ 26 + X ^ 22 + X ^ 4 + X) + remainder28 = 0 := by
  unfold remainder27 remainder28 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_28 :
    remainder28 ^ 2 + modulus * (X ^ 56 + X ^ 54 + X ^ 38 + X ^ 36 + X ^ 32 + X ^ 30 + X ^ 20 + X ^ 18 + X ^ 14 + X ^ 8 + X ^ 4 + 1) + remainder29 = 0 := by
  unfold remainder28 remainder29 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_29 :
    remainder29 ^ 2 + modulus * (X ^ 56 + X ^ 54 + X ^ 46 + X ^ 40 + X ^ 36 + X ^ 28 + X ^ 24 + X ^ 20 + X ^ 18 + X ^ 12 + X ^ 10 + X ^ 6 + X ^ 4) + remainder30 = 0 := by
  unfold remainder29 remainder30 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_30 :
    remainder30 ^ 2 + modulus * (X ^ 60 + X ^ 54 + X ^ 52 + X ^ 46 + X ^ 44 + X ^ 36 + X ^ 34 + X ^ 32 + X ^ 30 + X ^ 22 + X ^ 18 + X ^ 16 + X ^ 14 + X ^ 12 + X ^ 10 + X ^ 8 + X ^ 4 + 1) + remainder31 = 0 := by
  unfold remainder30 remainder31 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_31 :
    remainder31 ^ 2 + modulus * (X ^ 62 + X ^ 60 + X ^ 58 + X ^ 50 + X ^ 48 + X ^ 42 + X ^ 40 + X ^ 34 + X ^ 32 + X ^ 26 + X ^ 24 + X ^ 14 + X ^ 2 + X + 1) + remainder32 = 0 := by
  unfold remainder31 remainder32 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_32 :
    remainder32 ^ 2 + modulus * (X ^ 60 + X ^ 56 + X ^ 54 + X ^ 52 + X ^ 44 + X ^ 42 + X ^ 34 + X ^ 26 + X ^ 18 + X ^ 16 + X ^ 12 + X ^ 10 + X ^ 4 + X ^ 2) + remainder33 = 0 := by
  unfold remainder32 remainder33 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_33 :
    remainder33 ^ 2 + modulus * (X ^ 62 + X ^ 58 + X ^ 56 + X ^ 54 + X ^ 48 + X ^ 44 + X ^ 42 + X ^ 36 + X ^ 30 + X ^ 28 + X ^ 24 + X ^ 22 + X ^ 20 + X ^ 12 + X ^ 10 + X ^ 6 + X ^ 2 + X) + remainder34 = 0 := by
  unfold remainder33 remainder34 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_34 :
    remainder34 ^ 2 + modulus * (X ^ 62 + X ^ 58 + X ^ 56 + X ^ 52 + X ^ 48 + X ^ 46 + X ^ 38 + X ^ 34 + X ^ 30 + X ^ 28 + X ^ 22 + X ^ 16 + X ^ 14 + X ^ 10 + X) + remainder35 = 0 := by
  unfold remainder34 remainder35 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_35 :
    remainder35 ^ 2 + modulus * (X ^ 62 + X ^ 58 + X ^ 56 + X ^ 50 + X ^ 48 + X ^ 46 + X ^ 44 + X ^ 42 + X ^ 40 + X ^ 38 + X ^ 36 + X ^ 30 + X ^ 28 + X ^ 18 + X ^ 14 + X ^ 10 + X ^ 6 + X + 1) + remainder36 = 0 := by
  unfold remainder35 remainder36 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_36 :
    remainder36 ^ 2 + modulus * (X ^ 62 + X ^ 58 + X ^ 56 + X ^ 50 + X ^ 44 + X ^ 42 + X ^ 36 + X ^ 28 + X ^ 16 + X ^ 10 + X ^ 8 + X ^ 4 + X) + remainder37 = 0 := by
  unfold remainder36 remainder37 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2]

theorem square_certificate_37 :
    remainder37 ^ 2 + modulus * (X ^ 62 + X ^ 58 + X ^ 56 + X ^ 50 + X ^ 48 + X ^ 44 + X ^ 42 + X ^ 40 + X ^ 38 + X ^ 36 + X ^ 30 + X ^ 28 + X ^ 24 + X ^ 22 + X ^ 14 + X ^ 12 + X ^ 10 + X ^ 8 + X ^ 4 + X ^ 2 + X + 1) + remainder38 = 0 := by
  unfold remainder37 remainder38 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_38 :
    remainder38 ^ 2 + modulus * (X ^ 62 + X ^ 60 + X ^ 58 + X ^ 50 + X ^ 44 + X ^ 42 + X ^ 36 + X ^ 34 + X ^ 32 + X ^ 30 + X ^ 28 + X ^ 24 + X ^ 10 + X) + remainder39 = 0 := by
  unfold remainder38 remainder39 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_39 :
    remainder39 ^ 2 + modulus * (X ^ 54 + X ^ 42 + X ^ 38 + X ^ 36 + X ^ 30 + X ^ 22 + X ^ 20 + X ^ 16 + X ^ 14 + X ^ 12 + X ^ 4 + 1) + remainder40 = 0 := by
  unfold remainder39 remainder40 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_40 :
    remainder40 ^ 2 + modulus * (X ^ 56 + X ^ 50 + X ^ 48 + X ^ 46 + X ^ 36 + X ^ 28 + X ^ 26 + X ^ 22 + X ^ 18 + X ^ 12 + X ^ 10 + X ^ 4 + X ^ 2) + remainder41 = 0 := by
  unfold remainder40 remainder41 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_41 :
    remainder41 ^ 2 + modulus * (X ^ 60 + X ^ 54 + X ^ 50 + X ^ 48 + X ^ 44 + X ^ 42 + X ^ 40 + X ^ 36 + X ^ 32 + X ^ 30 + X ^ 28 + X ^ 20 + X ^ 16 + X ^ 14 + X ^ 12 + X ^ 10) + remainder42 = 0 := by
  unfold remainder41 remainder42 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_42 :
    remainder42 ^ 2 + modulus * (X ^ 62 + X ^ 60 + X ^ 58 + X ^ 52 + X ^ 50 + X ^ 46 + X ^ 44 + X ^ 42 + X ^ 34 + X ^ 32 + X ^ 30 + X ^ 18 + X ^ 16 + X ^ 14 + X ^ 12 + X ^ 10 + X ^ 8 + X ^ 6 + X ^ 4 + X ^ 2 + X + 1) + remainder43 = 0 := by
  unfold remainder42 remainder43 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_43 :
    remainder43 ^ 2 + modulus * (X ^ 56 + X ^ 54 + X ^ 46 + X ^ 44 + X ^ 40 + X ^ 38 + X ^ 34 + X ^ 32 + X ^ 28 + X ^ 22 + X ^ 10 + 1) + remainder44 = 0 := by
  unfold remainder43 remainder44 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2]

theorem square_certificate_44 :
    remainder44 ^ 2 + modulus * (X ^ 60 + X ^ 54 + X ^ 52 + X ^ 46 + X ^ 44 + X ^ 36 + X ^ 34 + X ^ 28 + X ^ 26 + X ^ 22 + X ^ 16 + X ^ 14 + X ^ 10 + X ^ 8 + X ^ 4 + X ^ 2 + 1) + remainder45 = 0 := by
  unfold remainder44 remainder45 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_45 :
    remainder45 ^ 2 + modulus * (X ^ 62 + X ^ 60 + X ^ 58 + X ^ 56 + X ^ 50 + X ^ 44 + X ^ 42 + X ^ 34 + X ^ 26 + X ^ 16 + X ^ 14 + X ^ 12 + X ^ 8 + X ^ 6 + X ^ 4 + X ^ 2 + X) + remainder46 = 0 := by
  unfold remainder45 remainder46 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_46 :
    remainder46 ^ 2 + modulus * (X ^ 60 + X ^ 56 + X ^ 52 + X ^ 50 + X ^ 48 + X ^ 42 + X ^ 40 + X ^ 38 + X ^ 32 + X ^ 30 + X ^ 24 + X ^ 22 + X ^ 20 + X ^ 16 + X ^ 10 + X ^ 8 + X ^ 6 + X ^ 4 + 1) + remainder47 = 0 := by
  unfold remainder46 remainder47 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_47 :
    remainder47 ^ 2 + modulus * (X ^ 62 + X ^ 58 + X ^ 54 + X ^ 52 + X ^ 50 + X ^ 46 + X ^ 36 + X ^ 34 + X ^ 28 + X ^ 26 + X ^ 24 + X ^ 16 + X ^ 14 + X ^ 8 + X ^ 6 + X ^ 4 + X ^ 2 + X) + remainder48 = 0 := by
  unfold remainder47 remainder48 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_48 :
    remainder48 ^ 2 + modulus * (X ^ 62 + X ^ 60 + X ^ 58 + X ^ 56 + X ^ 54 + X ^ 50 + X ^ 44 + X ^ 40 + X ^ 38 + X ^ 34 + X ^ 30 + X ^ 28 + X ^ 20 + X ^ 14 + X ^ 8 + X ^ 6 + X ^ 2 + X + 1) + remainder49 = 0 := by
  unfold remainder48 remainder49 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_49 :
    remainder49 ^ 2 + modulus * (X ^ 60 + X ^ 56 + X ^ 46 + X ^ 42 + X ^ 38 + X ^ 32 + X ^ 30 + X ^ 26 + X ^ 22 + X ^ 20 + X ^ 16 + X ^ 14 + X ^ 12 + X ^ 10 + X ^ 8 + X ^ 6 + X ^ 2 + 1) + remainder50 = 0 := by
  unfold remainder49 remainder50 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_50 :
    remainder50 ^ 2 + modulus * (X ^ 62 + X ^ 58 + X ^ 54 + X ^ 52 + X ^ 50 + X ^ 48 + X ^ 36 + X ^ 34 + X ^ 30 + X ^ 28 + X ^ 26 + X ^ 24 + X ^ 22 + X ^ 20 + X ^ 18 + X ^ 16 + X ^ 14 + X ^ 12 + X ^ 6 + X ^ 2 + X) + remainder51 = 0 := by
  unfold remainder50 remainder51 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_51 :
    remainder51 ^ 2 + modulus * (X ^ 62 + X ^ 60 + X ^ 58 + X ^ 56 + X ^ 54 + X ^ 52 + X ^ 50 + X ^ 44 + X ^ 34 + X ^ 20 + X ^ 16 + X ^ 14 + X ^ 6 + X) + remainder52 = 0 := by
  unfold remainder51 remainder52 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_52 :
    remainder52 ^ 2 + modulus * (X ^ 48 + X ^ 40 + X ^ 38 + X ^ 36 + X ^ 30 + X ^ 26 + X ^ 24 + X ^ 12 + X ^ 10 + X ^ 6 + X ^ 4) + remainder53 = 0 := by
  unfold remainder52 remainder53 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_53 :
    remainder53 ^ 2 + modulus * (X ^ 38 + X ^ 34 + X ^ 32 + X ^ 28 + X ^ 24 + X ^ 22 + X ^ 10 + X ^ 8 + X ^ 4 + X ^ 2 + 1) + remainder54 = 0 := by
  unfold remainder53 remainder54 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_54 :
    remainder54 ^ 2 + modulus * (X ^ 60 + X ^ 56 + X ^ 52 + X ^ 48 + X ^ 40 + X ^ 36 + X ^ 32 + X ^ 20 + X ^ 18 + X ^ 16 + X ^ 14 + X ^ 10 + X ^ 4 + X ^ 2) + remainder55 = 0 := by
  unfold remainder54 remainder55 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_55 :
    remainder55 ^ 2 + modulus * (X ^ 62 + X ^ 60 + X ^ 58 + X ^ 56 + X ^ 54 + X ^ 52 + X ^ 50 + X ^ 46 + X ^ 44 + X ^ 42 + X ^ 40 + X ^ 38 + X ^ 34 + X ^ 32 + X ^ 28 + X ^ 24 + X ^ 22 + X ^ 18 + X ^ 16 + X ^ 14 + X ^ 10 + X ^ 8 + X ^ 6 + X + 1) + remainder56 = 0 := by
  unfold remainder55 remainder56 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_56 :
    remainder56 ^ 2 + modulus * (X ^ 48 + X ^ 38 + X ^ 34 + X ^ 28 + X ^ 24 + X ^ 16 + X ^ 14 + X ^ 10 + X ^ 4 + X ^ 2) + remainder57 = 0 := by
  unfold remainder56 remainder57 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_57 :
    remainder57 ^ 2 + modulus * (X ^ 60 + X ^ 56 + X ^ 52 + X ^ 48 + X ^ 44 + X ^ 40 + X ^ 38 + X ^ 34 + X ^ 32 + X ^ 28 + X ^ 24 + X ^ 18 + X ^ 14 + X ^ 10 + X ^ 6 + X ^ 4 + 1) + remainder58 = 0 := by
  unfold remainder57 remainder58 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_58 :
    remainder58 ^ 2 + modulus * (X ^ 62 + X ^ 60 + X ^ 58 + X ^ 56 + X ^ 54 + X ^ 52 + X ^ 50 + X ^ 48 + X ^ 46 + X ^ 44 + X ^ 42 + X ^ 40 + X ^ 38 + X ^ 36 + X ^ 34 + X ^ 32 + X ^ 30 + X ^ 26 + X ^ 22 + X ^ 20 + X ^ 14 + X ^ 12 + X ^ 10 + X ^ 4 + X + 1) + remainder59 = 0 := by
  unfold remainder58 remainder59 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_59 :
    remainder59 ^ 2 + modulus * (X ^ 60 + X ^ 56 + X ^ 52 + X ^ 48 + X ^ 44 + X ^ 40 + X ^ 36 + X ^ 32 + X ^ 20 + X ^ 12 + X ^ 4 + 1) + remainder60 = 0 := by
  unfold remainder59 remainder60 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_60 :
    remainder60 ^ 2 + modulus * (X ^ 62 + X ^ 60 + X ^ 58 + X ^ 56 + X ^ 54 + X ^ 52 + X ^ 50 + X ^ 48 + X ^ 46 + X ^ 44 + X ^ 42 + X ^ 40 + X ^ 38 + X ^ 36 + X ^ 34 + X ^ 32 + X ^ 30 + X ^ 26 + X ^ 22 + X ^ 20 + X ^ 18 + X ^ 16 + X ^ 14 + X ^ 10 + X ^ 6 + X ^ 4 + X) + remainder61 = 0 := by
  unfold remainder60 remainder61 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_61 :
    remainder61 ^ 2 + modulus * (X ^ 28 + X ^ 24 + X ^ 20 + X ^ 16) + remainder62 = 0 := by
  unfold remainder61 remainder62 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_62 :
    remainder62 ^ 2 + modulus * (X ^ 60 + X ^ 56 + X ^ 52 + X ^ 48 + X ^ 44 + X ^ 40 + X ^ 36 + X ^ 32 + 1) + remainder63 = 0 := by
  unfold remainder62 remainder63 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2, cast_4]

theorem square_certificate_63 :
    remainder63 ^ 2 + modulus * (X ^ 62 + X ^ 60 + X ^ 58 + X ^ 56 + X ^ 54 + X ^ 52 + X ^ 50 + X ^ 48 + X ^ 46 + X ^ 44 + X ^ 42 + X ^ 40 + X ^ 38 + X ^ 36 + X ^ 34 + X ^ 32 + X ^ 30 + X ^ 28 + X ^ 26 + X ^ 24 + X ^ 22 + X ^ 20 + X ^ 18 + X ^ 16 + X ^ 14 + X ^ 12 + X ^ 10 + X ^ 8 + X ^ 6 + X ^ 4 + X) + remainder64 = 0 := by
  unfold remainder63 remainder64 modulus
  simp only [add_pow_char]
  ring_nf
  simp [cast_2]

/-- A full Bézout identity for the 32-squaring remainder plus `X`. -/
theorem bezout_certificate :
    (X ^ 60 + X ^ 57 + X ^ 48 + X ^ 46 + X ^ 41 + X ^ 38 + X ^ 37 + X ^ 35 + X ^ 32 + X ^ 26 + X ^ 25 + X ^ 22 + X ^ 21 + X ^ 20 + X ^ 18 + X ^ 17 + X ^ 15 + X ^ 12 + X ^ 11 + X ^ 7 + X ^ 5 + X ^ 3 + X ^ 2) * modulus +
      (X ^ 62 + X ^ 60 + X ^ 57 + X ^ 56 + X ^ 55 + X ^ 54 + X ^ 51 + X ^ 49 + X ^ 47 + X ^ 46 + X ^ 44 + X ^ 40 + X ^ 38 + X ^ 37 + X ^ 32 + X ^ 31 + X ^ 29 + X ^ 28 + X ^ 27 + X ^ 26 + X ^ 25 + X ^ 24 + X ^ 22 + X ^ 20 + X ^ 19 + X ^ 17 + X ^ 15 + X ^ 11 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 2 + X + 1) * (remainder32 + X) = 1 := by
  unfold remainder32 modulus
  ring_nf
  simp [cast_2, cast_4, cast_6, cast_8, cast_10, cast_12, cast_14, cast_16, cast_18]

end BulksketchBridge.Algebra.Gf64
