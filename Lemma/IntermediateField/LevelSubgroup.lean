import Mathlib

set_option autoImplicit false

namespace groupCohomology

variable {G : Type*} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

theorem comap_fixingSubgroup_eq_ker (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    F.fixingSubgroup.comap r
      = ((AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).comp r).ker := by
  rw [← @IntermediateField.restrictNormalHom_ker ℚ (AlgebraicClosure ℚ) _ _ _ F ‹Normal ℚ F›,
    MonoidHom.comap_ker]
  rfl


theorem comap_fixingSubgroup_antitone {F F' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : F ≤ F') :
    F'.fixingSubgroup.comap r ≤ F.fixingSubgroup.comap r :=
  Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone h)

end groupCohomology
