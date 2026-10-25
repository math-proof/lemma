-- Carved from Lemma/Definitions/Def_GroupCohomology_LevelQuotient.lean: instance decls only.
import Mathlib
import Instance.GroupCohomology_LevelSubgroup
import Instance.FieldTheory_RatAlgClosureGalois

set_option autoImplicit false

noncomputable section

namespace groupCohomology

scoped instance isAlgClosure_rat_algebraicClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩

variable {G : Type*} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

end groupCohomology


end
