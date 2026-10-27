import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b x y : ℝ}
-- given
  (h₀ : a = b)
  (_h₁ : x > y) :
-- imply
  a * x = b * x := by
-- proof
  rw [h₀]


-- created on 2019-04-03
