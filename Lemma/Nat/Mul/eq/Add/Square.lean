import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y z : ℂ} :
-- imply
  (z - x) * (z - y) = ((z - x) ^ 2 + (z - y) ^ 2 - (x - y) ^ 2) / 2 := by
-- proof
  ring


-- created on 2019-11-03
