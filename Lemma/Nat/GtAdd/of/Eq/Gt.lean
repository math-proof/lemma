import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a x b y : ℝ}
-- given
  (h₀ : a = x)
  (h₁ : b > y) :
-- imply
  a + b > x + y := by
-- proof
  linarith


-- created on 2021-08-12
