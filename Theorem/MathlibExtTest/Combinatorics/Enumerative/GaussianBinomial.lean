/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/GaussianBinomial.lean -/


import Def.Combinatorics.Enumerative.GaussianBinomial
import Lemma.Finset.Enumerative.GaussianBinomial
import Mathlib.Algebra.Ring.Nat
open MathlibExt


-- small case: G(2, 1) unfolds by one Pascal step to 1 + Q
example {R : Type*} [CommRing R] (Q : R) : gaussBinom Q 2 1 = 1 + Q := by
  calc gaussBinom Q 2 1
      = gaussBinom Q 1 0 + Q ^ 1 * gaussBinom Q 1 1 :=
        gaussBinom_succ_succ Q 1 0
    _ = 1 + Q := by rw [gaussBinom_zero_right, gaussBinom_self]; simp

-- vanishing: G(3, 5) = 0 since 3 < 5
example {R : Type*} [CommRing R] (Q : R) : gaussBinom Q 3 5 = 0 :=
  gaussBinom_eq_zero_of_lt Q 3 5 (by decide)

-- over ℕ: G_2(2, 1) = 3
example : gaussBinom (2 : ℕ) 2 1 = 3 := by
  calc gaussBinom (2 : ℕ) 2 1
      = gaussBinom (2 : ℕ) 1 0 + (2 : ℕ) ^ 1 * gaussBinom (2 : ℕ) 1 1 :=
        gaussBinom_succ_succ _ 1 0
    _ = 3 := by rw [gaussBinom_zero_right, gaussBinom_self]; rfl

-- two factors: P(2) = (1 - Q) * (1 - Q ^ 2)
example {R : Type*} [CommRing R] (Q : R) :
    qPochFin Q 2 = (1 - Q) * (1 - Q ^ 2) := by
  have h1 : qPochFin Q 1 = 1 - Q := by
    have h := qPochFin_succ Q 0
    simpa using h
  have h2 : qPochFin Q 2 = qPochFin Q 1 * (1 - Q ^ 2) := by
    have h := qPochFin_succ Q 1
    simpa using h
  rw [h2, h1]

-- product formula at M = 2, k = 1
example {R : Type*} [CommRing R] (Q : R) :
    gaussBinom Q 2 1 * qPochFin Q 1 * qPochFin Q (2 - 1) = qPochFin Q 2 :=
  gaussBinom_mul_qPochFin_mul_qPochFin Q 2 1 (by decide)

