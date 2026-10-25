import Mathlib
import sympy.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.PoissonUniqueness
open Filter Topology DifferentialOperators


namespace DifferentialOperators

/--
[SmoothZeroAtInfty.exists_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PoissonUniqueness.lean)
-/
@[path]
lemma SmoothZeroAtInfty.exists_norm_le
  {n : ℕ}
  {u : SmoothZeroAtInfty n} :
-- imply
  ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), ‖u x‖ ≤ C := by
-- proof
  have hcont : Continuous u := u.smooth.continuous
  have htend : Tendsto (fun x => ‖u x‖) (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
    have h0 := u.iteratedFDeriv_zero_at_infty 0
    simp only [norm_iteratedFDeriv_zero] at h0
    exact h0
  have hev : ∀ᶠ x in cocompact (EuclideanSpace ℝ (Fin n)), ‖u x‖ < 1 := by
    have := htend.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    filter_upwards [this] with x hx
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hx
  rw [Filter.hasBasis_cocompact.eventually_iff] at hev
  obtain ⟨K, hKc, hKp⟩ := hev
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨max M 1, fun x => by
    by_cases hx : x ∈ K
    · exact le_trans (hM x hx) (le_max_left _ _)
    · exact le_trans (le_of_lt (hKp hx)) (le_max_right _ _)⟩

end DifferentialOperators

namespace DifferentialOperators

/--
[eq_zero_of_const_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PoissonUniqueness.lean)
-/
@[path]
lemma eq_zero_of_const_tendsto_zero
  {n : ℕ}
  {c : ℂ}
-- given
  (hn : 0 < n)
  (h : Tendsto (fun _ : EuclideanSpace ℝ (Fin n) => c) (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0)) :
-- imply
  c = 0 := by
-- proof
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : NoncompactSpace (EuclideanSpace ℝ (Fin n)) := inferInstance
  exact tendsto_nhds_unique tendsto_const_nhds h
end DifferentialOperators



-- created on 2026-10-23
