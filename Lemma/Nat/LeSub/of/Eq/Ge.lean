import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y a b : ℝ}
-- given
  (h₀ : y = x)
  (h₁ : a ≥ b) :
-- imply
  x - a ≤ y - b := by
-- proof
  rw [h₀]
  linarith


-- created on 2019-04-26
