import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  [DecidableEq α]
  {y : α}
  {X : Finset α}
  {a : α → ℝ}
-- given
  (h₀ : y ∉ X)
  (h₁ : X.card ≠ 0)
  (h₂ : a y = (∑ x ∈ X, a x) / (X.card : ℝ)) :
-- imply
  (∑ z ∈ insert y X, a z) / ((insert y X).card : ℝ) = a y := by
-- proof
  have hcard : ((insert y X).card : ℝ) = (X.card : ℝ) + 1 := by
    simp [Finset.card_insert_of_notMem h₀]
  have hsum : ∑ z ∈ insert y X, a z = (∑ z ∈ X, a z) + a y := by
    simpa [add_comm] using Finset.sum_insert (f := a) h₀
  rw [hsum, hcard, h₂]
  field_simp [h₁]


-- created on 2021-04-03
-- updated on 2026-10-17
