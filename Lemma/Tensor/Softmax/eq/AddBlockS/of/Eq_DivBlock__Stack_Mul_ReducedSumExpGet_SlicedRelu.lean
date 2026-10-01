import sympy.functions.elementary.masked_softmax
import sympy.Basic


@[main]
private lemma main
  {n l u : ℕ}
  {A : Fin n → Fin n → ℝ}
  {z : Fin n → ℤ → ℝ}
-- given
  (h : ∀ i j : Fin n, ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) → z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) = Real.exp (A i j) / (∑ k ∈ Finset.univ.filter (fun k : Fin n => ((i.val : ℤ) - l < (k.val : ℤ) ∧ (k.val : ℤ) < (i.val : ℤ) + u)), Real.exp (A i k))) :
-- imply
  ∀ i j : Fin n, maskedSoftmax (fun j => (A i j)) (fun j : Fin n => if ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) then 1 else 0) j = if ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u) then z i ((j.val : ℤ) - i.val + ((l : ℤ) - 1)) else 0 := by
-- proof
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p
    ·
      simp [maskedExp, hp]
    ·
      simp [maskedExp, hp]
  intro i j
  simp only [maskedSoftmax, key]
  rw [← Finset.sum_filter]
  by_cases hp : ((i.val : ℤ) - l < (j.val : ℤ) ∧ (j.val : ℤ) < (i.val : ℤ) + u)
  ·
    simp only [if_pos hp]
    rw [h i j hp]
  ·
    simp only [if_neg hp, zero_div]


-- created on 2026-09-27
