import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.TangentCone.Real
import sympy.series.limits
import sympy.Basic
open scoped Topology


@[main]
private lemma main
  {f : ℝ → ℝ}
  {x : ℝ}
-- given
  (h : DifferentiableWithinAt ℝ f (Set.Ioi x) x) :
-- imply
  derivWithin f (Set.Ioi x) x = lim [ε → 0⁺] ((f (ε + x) - f x) / ε) := by
-- proof
  have hs : Filter.Tendsto (slope f x) (nhdsWithin x (Set.Ioi x))
    (𝓝 (derivWithin f (Set.Ioi x) x)) := by
    have hx : x ∉ Set.Ioi x := by simp
    rw [← hasDerivWithinAt_iff_tendsto_slope' hx]
    rw [HasDerivWithinAt.derivWithin h.hasDerivWithinAt (uniqueDiffWithinAt_Ioi x)]
    exact h.hasDerivWithinAt
  have trans : Filter.Tendsto (fun ε : ℝ => x + ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin x (Set.Ioi x)) := by
    rw [tendsto_nhdsWithin_iff]
    have hc : Filter.Tendsto (fun ε : ℝ => x + ε) (𝓝 0) (𝓝 x) := by
      simpa using (continuous_const_add x).tendsto 0
    refine ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Set.mem_Ioi] at hε ⊢
    linarith
  have key : Filter.Tendsto (fun ε : ℝ => (f (ε + x) - f x) / ε)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (derivWithin f (Set.Ioi x) x)) := by
    refine (hs.comp trans).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Set.mem_Ioi] at hε
    simp [slope, div_eq_inv_mul, add_comm x ε]
  rw [key.limUnder_eq]


-- created on 2026-10-08
