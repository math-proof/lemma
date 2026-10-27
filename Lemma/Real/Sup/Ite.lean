import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : α → ℝ}
  {S : Set α}
  {c : ℝ}
-- given
  (h₀ : S.Nonempty)
  (h₁ : BddAbove (f '' S))
  (h₂ : c ≤ sSup (f '' S)) :
-- imply
  sSup (insert c (f '' S)) = sSup (f '' S) := by
-- proof
  rw [csSup_insert h₁ (h₀.image f)]
  apply max_eq_right h₂


-- created on 2023-04-23
-- updated on 2026-10-26
