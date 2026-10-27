import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Def.Analysis.Real.Limits.Part4
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {g : ℝ → ℝ}
  {x₀ y : ℝ}
-- given
  (h : lim [x → x₀] g x = y)
  (hy : y ∈ Ioi 0) :
-- imply
  lim [x → x₀] |g x| = lim [x → x₀] g x := by
-- proof
  rw [h.limUnder_eq, ← abs_of_pos (Set.mem_Ioi.mp hy)]
  exact h.abs


-- created on 2023-04-18
