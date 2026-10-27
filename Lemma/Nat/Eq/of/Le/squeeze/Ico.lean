import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x b : ℤ}
-- given
  (h₀ : x ≥ b)
  (h : x ≤ b) :
-- imply
  x = b := by
-- proof
  exact le_antisymm h h₀


-- created on 2021-08-28
