import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y a b : ℝ}
-- given
  (h₀ : a = b)
  (_h₁ : x > y) :
-- imply
  a / (x - y) = b / (x - y) := by
-- proof
  rw [h₀]


-- created on 2019-04-02
