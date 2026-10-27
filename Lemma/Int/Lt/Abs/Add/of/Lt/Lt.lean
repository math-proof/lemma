import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y a b : ℝ}
-- given
  (h₀ : |x| < a)
  (h₁ : |y| < b) :
-- imply
  |x + y| < a + b := by
-- proof
  exact (abs_add_le x y).trans_lt (add_lt_add h₀ h₁)


-- created on 2020-01-06
