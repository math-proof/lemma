import Mathlib.Basic.Real.Sign
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x > 0) :
-- imply
  Real.sign x = 1 := by
-- proof
  exact Real.sign_of_pos h


-- created on 2023-05-29
