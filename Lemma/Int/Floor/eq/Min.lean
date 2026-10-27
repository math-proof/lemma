import Mathlib.Algebra.Order.Floor.Ring
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ} :
-- imply
  ⌊min x y⌋ = min ⌊x⌋ ⌊y⌋ := by
-- proof
  exact Int.floor_mono.map_min


-- created on 2019-05-13
