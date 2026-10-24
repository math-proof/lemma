/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/FermatQuotient.lean -/

import sympy.atlas.NumberTheory.FermatQuotient
import Lemma.Int.FermatQuotient

-- Small exact values via the public evaluation theorem.

example : Int.fermatQuotient 3 (by decide) (2 : ℤ) (by decide) = 1 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

example : Int.fermatQuotient 5 (by decide) (2 : ℤ) (by decide) = 3 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

example : Int.fermatQuotient 3 (by decide) (4 : ℤ) (by decide) = 5 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

-- Evaluation lemma is definitionally `rfl`.
example : Int.fermatQuotient 5 (by decide) (2 : ℤ) (by decide) =
    ((2 : ℤ) ^ (4 : ℕ) - 1) / (5 : ℤ) :=
  Int.fermatQuotient_eq 5 (by decide) (2 : ℤ) (by decide)

-- Source-motivated specialization at `a = 2` for an odd prime.
example : Int.fermatQuotient 7 (by decide) (2 : ℤ) (by decide) = 9 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

-- Boundary prime `p = 2`.
example : Int.fermatQuotient 2 (by decide) (3 : ℤ) (by decide) = 1 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

example : Int.fermatQuotient 2 (by decide) (-1 : ℤ) (by decide) = -1 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

-- Negative integer input with odd prime.
example : Int.fermatQuotient 3 (by decide) (-2 : ℤ) (by decide) = 1 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

example : Int.fermatQuotient 5 (by decide) (-2 : ℤ) (by decide) = 3 := by
  simp only [Int.fermatQuotient_eq]
  norm_num

-- Public recovery theorem applied on concrete cases.
example : (3 : ℤ) * Int.fermatQuotient 3 (by decide) (2 : ℤ) (by decide) =
    (2 : ℤ) ^ (2 : ℕ) - 1 :=
  Int.natCast_mul_fermatQuotient 3 (by decide) (2 : ℤ) (by decide)

example : (5 : ℤ) * Int.fermatQuotient 5 (by decide) (2 : ℤ) (by decide) =
    (2 : ℤ) ^ (4 : ℕ) - 1 :=
  Int.natCast_mul_fermatQuotient 5 (by decide) (2 : ℤ) (by decide)
