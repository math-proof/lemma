-- Carved from Lemma/Definitions/Def_GroupCohomology_LevelSubgroup.lean: instance decls only.
import Mathlib

set_option autoImplicit false

namespace groupCohomology

variable {G : Type*} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))


instance normal_comap_fixingSubgroup (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] :
    (F.fixingSubgroup.comap r).Normal := by
  rw [comap_fixingSubgroup_eq_ker]; exact MonoidHom.normal_ker _

instance finiteIndex_comap_fixingSubgroup (F : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ F] [Normal ℚ F] : (F.fixingSubgroup.comap r).FiniteIndex := by
  rw [comap_fixingSubgroup_eq_ker]; exact Subgroup.finiteIndex_ker _


end groupCohomology
