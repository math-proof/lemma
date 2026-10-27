import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y a b : ℝ}
-- given
  (h₀ : x = y)
  (h₁ : a ≤ b) :
-- imply
  x - a ≥ y - b := by
-- proof
  linarith


-- created on 2021-08-05
