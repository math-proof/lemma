import Mathlib.LinearAlgebra.Matrix.Block
import Initialize.Tactic.Attr.Basic
import Syntax.LinearAlgebra.Matrix.Notation
open Matrix


/--
Determinant of the lower-triangular choose × binomial-transform matrix:
\((x-l)^{nd}\).
-/
@[path]
private lemma main
  [Field α]
  {n d : ℕ}
  {x l : α} :
-- imply
  ([i < n, j < n]
      ((i : ℕ).choose j : α) *
        ∑ h ∈ Finset.range (d + 1),
          (d.choose h : α) * (-l) ^ (d - h) * x ^ h *
            (h : α) ^ (i - j : ℤ)).det =
    (x - l) ^ (n * d) := by
-- proof
  rw [det_of_isLowerTriangular _ (fun i j (hij : i < j) => by
    simp only [Matrix.ofFun_apply]
    rw [Nat.choose_eq_zero_of_lt (show (i : ℕ) < j from hij), Nat.cast_zero, zero_mul])]
  simp only [Matrix.ofFun_apply, Nat.choose_self, Nat.cast_one, one_mul]
  have hdiag : ∀ i : Fin n,
      ∑ h ∈ Finset.range (d + 1),
          (d.choose h : α) * (-l) ^ (d - h) * x ^ h *
            (h : α) ^ (i - i : ℤ) =
        (x - l) ^ d := by
    intro i
    have hexp : ∀ h : ℕ, (h : α) ^ (i - i : ℤ) = 1 := by
      intro h
      simp
    simp only [hexp, mul_one]
    rw [sub_eq_add_neg, add_pow]
    refine Finset.sum_congr rfl fun h _ => ?_
    ring
  simp only [hdiag]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]


-- created on 2026-10-24
