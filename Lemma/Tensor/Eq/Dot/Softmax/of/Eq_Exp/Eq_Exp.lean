import sympy.functions.elementary.masked_softmax
import sympy.Basic


@[main]
private lemma cross_attention
  {n h d_z : ℕ}
  {A : Fin n → Fin n → ℝ}
  {V : Fin n → Fin d_z → ℝ} :
-- imply
  (fun i t => ∑ j, maskedSoftmax (A i) (fun j => if ¬(i.val < h ↔ j.val < h) then 1 else 0) j * V j t) =
    fun i t => ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬(i.val < h ↔ j.val < h)),
      Real.exp (A i j) / (∑ k ∈ Finset.univ.filter (fun k : Fin n => ¬(i.val < h ↔ k.val < h)), Real.exp (A i k)) * V j t := by
-- proof
  have key : ∀ (p : Prop) [Decidable p] (x : ℝ), maskedExp x (if p then 1 else 0) = if p then Real.exp x else 0 := by
    intro p _ x
    by_cases hp : p
    ·
      simp [maskedExp, hp]
    ·
      simp [maskedExp, hp]
  funext i t
  simp only [maskedSoftmax, key, ite_div, zero_div, ite_mul, zero_mul, Finset.sum_filter]


-- created on 2026-09-27
