import Mathlib.Topology.Algebra.InfiniteSum.Defs
import sympy.series.limits
import sympy.Basic


@[path]
private lemma main
  [AddCommMonoid α]
  [TopologicalSpace α]
  {s : ℕ → α}
-- given
  (h : Summable s) :
-- imply
  lim [n → ∞] ∑ k ∈ Finset.range n, s k = ∑' k, s k := by
-- proof
  exact h.hasSum.tendsto_sum_nat


-- created on 2023-04-16
-- updated on 2026-09-06
