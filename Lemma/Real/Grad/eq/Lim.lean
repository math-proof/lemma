import Mathlib.Analysis.Calculus.Deriv.Slope
import sympy.series.limits
import sympy.Basic
open scoped Topology


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x : ℝ}
-- given
  (h : DifferentiableAt ℝ f x) :
-- imply
  deriv f x = lim [ε → 0] ((f (x + ε) - f x) / ε) := by
-- proof
  have key : Filter.Tendsto (fun ε : ℝ => (f (x + ε) - f x) / ε)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (𝓝 (deriv f x)) := by
    have hsub : Filter.Tendsto (fun ε : ℝ => x + ε)
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhdsWithin x {x}ᶜ) := by
      rw [tendsto_nhdsWithin_iff]
      have hc : Filter.Tendsto (fun ε : ℝ => x + ε) (𝓝 0) (𝓝 x) := by
        simpa using (continuous_const_add x).tendsto 0
      refine ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with ε hε
      simp only [Set.mem_compl_singleton_iff] at hε ⊢
      simpa using hε
    have hs := Filter.Tendsto.comp (hasDerivAt_iff_tendsto_slope.mp h.hasDerivAt) hsub
    refine hs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [Set.mem_compl_singleton_iff] at hε
    simp [slope, div_eq_inv_mul]
  rw [key.limUnder_eq]


-- created on 2026-10-08
