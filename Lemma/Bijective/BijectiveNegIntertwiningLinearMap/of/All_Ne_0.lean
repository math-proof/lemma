import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.SL2RealizationBridge
open Complex PrincipalSeriesBridge


namespace PrincipalSeriesBridge

/--
[neg_intertwining_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2RealizationBridge.lean)
-/
@[path]
lemma neg_intertwining_bijective
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  {s : ℂ}
  {ε : ZMod 2}
  {R₁ : SL2IrredGKModule.Realization (.principalSeries s ε) 𝔤 K 𝔨 Ad}
  {R₂ : SL2IrredGKModule.Realization (.principalSeries (-s) ε) 𝔤 K 𝔨 Ad}
  {b₁ : PrincipalSeriesBridge s ε R₁}
  {b₂ : PrincipalSeriesBridge (-s) ε R₂}
  {c : ℤ → ℂ}
-- given
  (hc : ∀ m : ℤ, c m ≠ 0) :
-- imply
  Function.Bijective (neg_intertwining_linearMap b₁ b₂ c) := by
-- proof
  have h_neg_bij : Function.Bijective (principalSeries_neg_map c) := by
    constructor
    · intro f g hfg
      ext m
      have hm : (principalSeries_neg_map c) f m = (principalSeries_neg_map c) g m := by
        rw [hfg]
      simp only [principalSeries_neg_map, LinearMap.coe_mk, AddHom.coe_mk] at hm
      exact mul_left_cancel₀ (hc m) hm
    · intro f
      exact ⟨fun m => (c m)⁻¹ * f m, by
        ext m
        simp only [principalSeries_neg_map, LinearMap.coe_mk, AddHom.coe_mk]
        rw [← mul_assoc, mul_inv_cancel₀ (hc m), one_mul]⟩
  have hb₁ := b₁.toModel.bijective
  have hb₂ := b₂.toModel.symm.bijective
  exact hb₂.comp (h_neg_bij.comp hb₁)
end PrincipalSeriesBridge



-- created on 2026-10-23
