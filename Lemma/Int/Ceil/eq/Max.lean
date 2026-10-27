import Mathlib.Algebra.Order.Floor.Ring
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x y : ℝ} :
-- imply
  ⌈max x y⌉ = max ⌈x⌉ ⌈y⌉ := by
-- proof
  exact Int.ceil_mono.map_max


-- created on 2019-03-10
