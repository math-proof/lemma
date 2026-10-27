import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma transport.given
  {x y a : ℝ}
-- given
  (h : x = y - a) :
-- imply
  x + a = y := by
-- proof
  rw [h]
  ring


-- created on 2022-04-01
