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
  (h₀ : lim [x → x₀] g x = y)
  (h₁ : y ∈ Iio 0) :
-- imply
  lim [x → x₀] |g x| = -lim [x → x₀] g x := by
-- proof
  rw [h₀.limUnder_eq, ← abs_of_neg (Set.mem_Iio.mp h₁)]
  exact h₀.abs


-- created on 2023-04-18
