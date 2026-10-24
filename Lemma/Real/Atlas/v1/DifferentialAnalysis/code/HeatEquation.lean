import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.HeatEquation
open TemperedDistribution LineDeriv DifferentialOperators in
open scoped SchwartzMap
open set on which `u` vanishes). -/


namespace DifferentialOperators

/--
[distributionVanishesOn_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquation.lean)
-/
@[path]
lemma distributionVanishesOn_sub
  {n : ℕ}
  {u v : 𝓢'(SpaceTime n, ℂ)}
  {U : Set (SpaceTime n)}
-- given
  (hu : DistributionVanishesOn n u U)
  (hv : DistributionVanishesOn n v U) :
-- imply
  DistributionVanishesOn n (u - v) U := by
-- proof
  intro φ hφ
  rw [show (u - v) φ = u φ - v φ from rfl, hu φ hφ, hv φ hφ, sub_self]

end DifferentialOperators

namespace DifferentialOperators

/--
[distributionalSupport_sub_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquation.lean)
-/
@[path]
lemma distributionalSupport_sub_subset
  {n : ℕ}
  {u v : 𝓢'(SpaceTime n, ℂ)} :
-- imply
  distributionalSupport n (u - v) ⊆ distributionalSupport n u ∪ distributionalSupport n v := by
-- proof
  intro x hx
  by_contra h
  simp only [Set.mem_union, not_or] at h
  obtain ⟨hnu, hnv⟩ := h
  simp only [distributionalSupport, Set.mem_setOf_eq, not_not] at hnu hnv
  obtain ⟨U₁, hU₁_open, hx_U₁, hU₁⟩ := hnu
  obtain ⟨U₂, hU₂_open, hx_U₂, hU₂⟩ := hnv
  exact hx ⟨U₁ ∩ U₂, hU₁_open.inter hU₂_open, ⟨hx_U₁, hx_U₂⟩,
    distributionVanishesOn_sub n
      (fun φ hφ => hU₁ φ (hφ.trans Set.inter_subset_left))
      (fun φ hφ => hU₂ φ (hφ.trans Set.inter_subset_right))⟩

end DifferentialOperators

namespace DifferentialOperators

/--
[supportedInTimeGeq_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquation.lean)
-/
@[path]
lemma supportedInTimeGeq_sub
  {n : ℕ}
  {u v : 𝓢'(SpaceTime n, ℂ)}
  {a b : ℝ}
-- given
  (ha : SupportedInTimeGeq n u a)
  (hb : SupportedInTimeGeq n v b) :
-- imply
  SupportedInTimeGeq n (u - v) (min a b) := by
-- proof
  intro x hx
  have hsub := distributionalSupport_sub_subset n u v hx
  simp only [Set.mem_union] at hsub
  simp only [Set.mem_setOf_eq]
  obtain hu | hv := hsub
  · exact le_trans (min_le_left a b) (ha hu)
  · exact le_trans (min_le_right a b) (hb hv)

end DifferentialOperators

namespace DifferentialOperators

/--
[compact_support_time_bounded_below](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquation.lean)
-/
@[path]
lemma compact_support_time_bounded_below
  {n : ℕ}
  {f : 𝓢'(SpaceTime n, ℂ)}
-- given
  (hf : HasCompactDistributionalSupport n f) :
-- imply
  ∃ b : ℝ, SupportedInTimeGeq n f b := by
-- proof
  by_cases hempty : (distributionalSupport n f) = ∅
  · exact ⟨0, fun x hx => (hempty ▸ hx : x ∈ (∅ : Set _)).elim⟩
  · have hne : Set.Nonempty (distributionalSupport n f) := Set.nonempty_iff_ne_empty.mpr hempty
    have hcont : Continuous (timeCoord n) :=
      PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0
    obtain ⟨x₀, _, hx₀_min⟩ := hf.exists_isMinOn hne hcont.continuousOn
    exact ⟨timeCoord n x₀, fun x hx => hx₀_min hx⟩
end DifferentialOperators
open DifferentialOperators in
/-- The forward fundamental solution of the heat operator on `SpaceTime n`: a
tempered distribution `E` such that `(∂ₜ − Δ) E = δ₀` and `E` is supported
in `{t ≥ 0}`. -/
namespace DifferentialOperators

end DifferentialOperators

namespace DifferentialOperators

/--
[heatOperator_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/HeatEquation.lean)
-/
@[path]
lemma heatOperator_sub
  {n : ℕ}
  {u v : 𝓢'(SpaceTime n, ℂ)} :
-- imply
  heatOperator n (u - v) = heatOperator n u - heatOperator n v := by
-- proof
  simp only [heatOperator, positiveSpatialLaplacian, sub_eq_add_neg,
    lineDerivOp_add, lineDerivOp_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  abel
end DifferentialOperators



-- created on 2026-10-23
