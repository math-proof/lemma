import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import sympy.Basic
open Filter Finset Topology


@[main]
private lemma main
  {T x : ℕ → ℝ}
  {c : ℝ}
-- given
  (h₀ : ∀ n, 0 < T n)
  (h₁ : Tendsto (fun n => ∑ k ∈ range n, T k) atTop atTop)
  (h₂ : ∀ n, 0 ≤ x n)
  (h₃ : Summable fun n => T n * x n)
  (h₄ : Tendsto x atTop (𝓝 c)) :
-- imply
  c = 0 := by
-- proof
  have hc : 0 ≤ c := ge_of_tendsto' h₄ h₂
  refine hc.antisymm' (not_lt.1 fun hpos => ?_)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h₄.eventually (lt_mem_nhds (half_lt_self hpos)))
  have hT : Summable fun n => T (n + N) * (c / 2) :=
    Summable.of_nonneg_of_le (fun n => by have := h₀ (n + N); positivity)
      (fun n => mul_le_mul_of_nonneg_left (hN _ (by omega)).le (h₀ _).le) ((summable_nat_add_iff N).2 h₃)
  have hT : Summable T := (summable_nat_add_iff N).1 ((summable_mul_right_iff (by positivity)).1 hT)
  exact not_tendsto_atTop_of_tendsto_nhds hT.hasSum.tendsto_sum_nat h₁


-- created on 2026-09-26