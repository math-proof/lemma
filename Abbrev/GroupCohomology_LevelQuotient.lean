import Mathlib
import Instance.GroupCohomology_LevelSubgroup
import Instance.FieldTheory_RatAlgClosureGalois
import Instance.GroupCohomology_LevelQuotient

set_option autoImplicit false

noncomputable section

namespace groupCohomology

variable {G : Type*} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

abbrev levelRestrict (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] : G →* (F ≃ₐ[ℚ] F) :=
  (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).comp r

end groupCohomology

namespace Rep

open scoped groupCohomology

end Rep

end
