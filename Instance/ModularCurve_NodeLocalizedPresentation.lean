-- Carved from Lemma/Definitions/Def_ModularCurve_NodeLocalizedPresentation.lean: instance decls only.
import Mathlib

set_option autoImplicit false

noncomputable section

namespace ModularCurve
namespace NodeLocalized

open MvPolynomial

section Presentation

variable (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k) (a b : k)


instance algebraEvalRange : Algebra (evalRange N A) (modularLocalizedAtPoint N A red a b) :=
  (Subring.inclusion (evalRange_le N A red a b)).toAlgebra


section KerLE

variable [hker : Fact (RingHom.ker (modularEval N A) ≤ RingHom.ker (pointEval A red a b))]


instance isLocalization_nodeDenominators :
    IsLocalization (nodeDenominators N A red a b) (modularLocalizedAtPoint N A red a b) where
  map_units := by
    rintro ⟨_, s, hs, rfl⟩
    rw [algebraMap_evalRange_rangeRestrict]
    exact isUnit_modularEvalAt N A red a b hs
  surj := fun z => by
    obtain ⟨r, s, hs, h⟩ := z.2
    exact ⟨⟨(modularEval N A).rangeRestrict r, ⟨(modularEval N A).rangeRestrict s,
      rangeRestrict_mem_nodeDenominators N A red a b hs⟩⟩, Subtype.ext h⟩
  exists_of_eq := fun {x y} h => ⟨1, by
    simp only [OneMemClass.coe_one, one_mul]
    exact Subtype.ext (congrArg (fun w : modularLocalizedAtPoint N A red a b => (w : LaurentSeries L)) h)⟩

instance isLocalRing_modularLocalizedAtPoint : IsLocalRing (modularLocalizedAtPoint N A red a b) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun z => ?_
  obtain ⟨r, s, hs, h⟩ := z.2
  have hs0 := modularEval_ne_zero_of_pointEval_ne_zero N A red a b hs
  have hz : (z : LaurentSeries L) = modularEval N A r * (modularEval N A s)⁻¹ := by
    rw [← h, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  by_cases hr : pointEval A red a b r = 0
  · right
    have hsr : pointEval A red a b (s - r) ≠ 0 := by rw [map_sub, hr, sub_zero]; exact hs
    have hsr0 := modularEval_ne_zero_of_pointEval_ne_zero N A red a b hsr
    have hsr0' : modularEval N A s - modularEval N A r ≠ 0 := by rwa [map_sub] at hsr0
    refine isUnit_iff_exists_inv.mpr ⟨⟨modularEval N A s * (modularEval N A (s - r))⁻¹, s, s - r, hsr, ?_⟩, Subtype.ext ?_⟩
    · rw [mul_assoc, inv_mul_cancel₀ hsr0, mul_one]
    · show (1 - (z : LaurentSeries L)) * (modularEval N A s * (modularEval N A (s - r))⁻¹) = 1
      rw [hz, map_sub]
      field_simp
  · left
    have hr0 := modularEval_ne_zero_of_pointEval_ne_zero N A red a b hr
    refine isUnit_iff_exists_inv.mpr ⟨⟨modularEval N A s * (modularEval N A r)⁻¹, s, r, hr, ?_⟩, Subtype.ext ?_⟩
    · rw [mul_assoc, inv_mul_cancel₀ hr0, mul_one]
    · show (z : LaurentSeries L) * (modularEval N A s * (modularEval N A r)⁻¹) = 1
      rw [hz]
      field_simp

end KerLE


end Presentation

end NodeLocalized
end ModularCurve

end
