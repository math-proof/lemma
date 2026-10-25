import Mathlib
import sympy.Basic
import Def.v1.Atlas.RealAnalysis.code.ContinuousFunctions.Limits
open Filter Topology Set ContinuousFunctions


namespace ContinuousFunctions

/--
[cluster_point_iff_acc_point](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/ContinuousFunctions/Limits.lean)
-/
@[path]
lemma cluster_point_iff_acc_point
  {S : Set ℝ}
  {x : ℝ} :
-- imply
  IsClusterPoint S x ↔ AccPt x (𝓟 S) := by
-- proof
  rw [accPt_iff_nhds]
  constructor
  · intro h U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨y, hyS, hyx, habs⟩ := h ε hε
    refine ⟨y, ⟨?_, hyS⟩, hyx⟩
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    linarith [abs_sub_comm y x]
  · intro h δ hδ
    obtain ⟨y, ⟨hyU, hyS⟩, hyx⟩ := h _ (Metric.ball_mem_nhds x hδ)
    refine ⟨y, hyS, hyx, ?_⟩
    have := Metric.mem_ball.mp hyU
    rw [Real.dist_eq] at this
    linarith [abs_sub_comm y x]

end ContinuousFunctions

namespace ContinuousFunctions

/--
[function_limit_iff_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/ContinuousFunctions/Limits.lean)
-/
@[path]
lemma function_limit_iff_tendsto
  {f : ℝ → ℝ}
  {S : Set ℝ}
  {c L : ℝ} :
-- imply
  FunctionConvergesAt f S c L ↔ Filter.Tendsto f (nhdsWithin c (S \ {c})) (nhds L) := by
-- proof
  rw [Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hfx⟩ := h ε hε
    refine ⟨δ, hδ, fun {x} hxmem hdist => ?_⟩
    rw [Real.dist_eq] at hdist ⊢
    exact hfx x hxmem.1 (abs_pos.mpr (sub_ne_zero.mpr hxmem.2)) hdist
  · intro h ε hε
    obtain ⟨δ, hδ, hfx⟩ := h ε hε
    refine ⟨δ, hδ, fun x hxS hpos hdist => ?_⟩
    have hxc : x ≠ c := by
      intro heq
      simp [heq] at hpos
    have hxmem : x ∈ S \ {c} := ⟨hxS, hxc⟩
    have hdist' : dist x c < δ := by rwa [Real.dist_eq]
    have := hfx hxmem hdist'
    rwa [Real.dist_eq] at this

end ContinuousFunctions

namespace ContinuousFunctions

/--
[function_limit_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/ContinuousFunctions/Limits.lean)
-/
@[path]
lemma function_limit_unique
  {f : ℝ → ℝ}
  {S : Set ℝ}
  {c L₁ L₂ : ℝ}
-- given
  (hc : IsClusterPoint S c)
  (hL₁ : FunctionConvergesAt f S c L₁)
  (hL₂ : FunctionConvergesAt f S c L₂) :
-- imply
  L₁ = L₂ := by
-- proof
  have hne : (nhdsWithin c (S \ {c})).NeBot := by
    rwa [← accPt_principal_iff_nhdsWithin, ← cluster_point_iff_acc_point]
  exact tendsto_nhds_unique
    ((function_limit_iff_tendsto f S c L₁).mp hL₁)
    ((function_limit_iff_tendsto f S c L₂).mp hL₂)

end ContinuousFunctions


-- created on 2026-10-23
