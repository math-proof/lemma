import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a x b : ℝ}
-- given
  (h₀ : b ≥ x)
  (h₁ : a = b) :
-- imply
  a ≥ x := by
-- proof
  rw [h₁]
  exact h₀


-- created on 2019-05-15
