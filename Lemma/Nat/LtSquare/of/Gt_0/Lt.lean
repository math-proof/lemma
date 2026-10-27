import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x M : ℝ}
-- given
  (h₀ : x > 0)
  (h₁ : x < M) :
-- imply
  x * x < M * M := by
-- proof
  nlinarith


-- created on 2019-08-28
