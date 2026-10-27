import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : a < x)
  (h₁ : b = x) :
-- imply
  b > a := by
-- proof
  rw [h₁]
  exact h₀


-- created on 2019-12-12
