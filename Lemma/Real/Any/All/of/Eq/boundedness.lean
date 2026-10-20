import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import sympy.Basic


@[path]
private lemma main
  {f : ℕ → ℝ}
  {a : ℝ}
-- given
  (h₀ : Filter.Tendsto f Filter.atTop (nhds a)) :
-- imply
  ∃ M > 0, ∀ n, |f n| ≤ M := by
-- proof
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h₀ 1 one_pos
  refine ⟨|a| + 1 + ∑ n ∈ Finset.range N, |f n|, ?_, ?_⟩
  ·
    positivity
  ·
    intro n
    if hn : n < N then
      have hs : |f n| ≤ ∑ i ∈ Finset.range N, |f i| :=
        Finset.single_le_sum (fun i hi => abs_nonneg (f i)) (Finset.mem_range.mpr hn)
      linarith [abs_nonneg a]
    else
      have hlt : |f n - a| < 1 := by
        simpa [Real.dist_eq] using hN n (le_of_not_gt hn)
      have hle : |f n| - |a| ≤ |f n - a| := by
        simpa [abs_sub_comm] using abs_sub_abs_le_abs_sub (f n) a
      have hsum : 0 ≤ ∑ i ∈ Finset.range N, |f i| :=
        Finset.sum_nonneg fun i hi => abs_nonneg (f i)
      linarith


-- created on 2020-05-16
-- updated on 2026-10-17
