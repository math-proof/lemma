import sympy.series.limits
import sympy.Basic
open scoped Topology


@[main]
private lemma main
  {f : ℝ → ℝ}
  {x₀ : ℝ}
-- given
  (h : ContinuousAt f x₀) :
-- imply
  lim [x → x₀] (f x) = f x₀ :=
  -- proof
  h.tendsto.mono_left nhdsWithin_le_nhds


-- created on 2026-10-08
