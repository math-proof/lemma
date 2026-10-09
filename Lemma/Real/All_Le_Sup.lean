import Lemma.Real.All_GeSup


@[path]
private lemma main
  {S : Set α}
  {f : α → ℝ}
-- given
  (h : BddAbove (f '' S)) :
-- imply
  ∀ x ∈ S, f x ≤ sSup (f '' S) := by
-- proof
  have h₁ := Real.All_GeSup h
  exact h₁


-- created on 2023-03-28
