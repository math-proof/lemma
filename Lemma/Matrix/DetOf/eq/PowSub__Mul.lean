import Lemma.Matrix.Det.eq.Prod.of.All_All_Eq_0
import sympy.Basic
open Matrix


/--
Determinant of the lower-triangular choose × binomial-transform matrix:
\((x-l)^{dn}\).
-/
@[path]
private lemma main
  {n d : ℕ}
  {x l : ℝ} :
-- imply
  (Matrix.of fun (i j : Fin n) =>
      ((i : ℕ).choose j : ℝ) *
        ∑ h ∈ Finset.range (d + 1),
          (d.choose h : ℝ) * (-l) ^ (d - h) * x ^ h *
            (h : ℝ) ^ (i - j : ℤ)).det =
    (x - l) ^ (d * n) := by
-- proof
  rw [Det.eq.Prod.of.All_All_Eq_0]
  ·
    simp only [Matrix.of_apply, Nat.choose_self, Nat.cast_one, one_mul]
    have hdiag : ∀ i : Fin n,
        ∑ h ∈ Finset.range (d + 1),
            (d.choose h : ℝ) * (-l) ^ (d - h) * x ^ h *
              (h : ℝ) ^ (i - i : ℤ) =
          (x - l) ^ d := by
      intro i
      have hexp : ∀ h : ℕ, (h : ℝ) ^ (i - i : ℤ) = 1 := by
        intro h
        simp
      simp only [hexp, mul_one]
      rw [sub_eq_add_neg, add_pow]
      refine Finset.sum_congr rfl fun h _ => ?_
      ring
    simp only [hdiag]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
  ·
    intro i j hij
    simp only [Matrix.of_apply]
    rw [Nat.choose_eq_zero_of_lt (show (i : ℕ) < j from hij), Nat.cast_zero, zero_mul]


-- created on 2026-10-24
