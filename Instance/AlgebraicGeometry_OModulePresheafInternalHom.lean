-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_OModulePresheafInternalHom.lean: instance decls only.
import Mathlib

import Def.AlgebraicGeometry_OModulePresheafHom
import Lemma.AlgebraicGeometry.OModulePresheafInternalHom

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F G : OModulePresheaf π)

instance smulSections (U : V.Opens) : SMul Γ(V, U) (homSub F G U) := ⟨sectionsSMul F G U⟩

instance moduleSectionsHomSub (U : V.Opens) : Module Γ(V, U) (homSub F G U) where
  one_smul φ := by
    ext W x; simp only [sections_smul_apply, map_one, one_smul]
  mul_smul a b φ := by
    ext W x; simp only [sections_smul_apply, map_mul, mul_smul]
  smul_zero a := by
    ext W x
    simp only [sections_smul_apply, Submodule.coe_zero, Pi.zero_apply, LinearMap.zero_apply, smul_zero]
  smul_add a φ ψ := by
    ext W x
    simp only [sections_smul_apply, Submodule.coe_add, Pi.add_apply, LinearMap.add_apply, smul_add]
  add_smul a b φ := by
    ext W x
    simp only [sections_smul_apply, map_add, add_smul, Submodule.coe_add, Pi.add_apply, LinearMap.add_apply]
  zero_smul φ := by
    ext W x
    simp only [sections_smul_apply, map_zero, zero_smul, Submodule.coe_zero, Pi.zero_apply, LinearMap.zero_apply]


end OModulePresheaf

end AlgebraicGeometry

end
