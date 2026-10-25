-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_ThetaGroup.lean: instance decls only.
import Mathlib
import Def.AlgebraicGeometry_RiemannForm
import Lemma.AlgebraicGeometry.ThetaGroup

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory AlgebraicGeometry NeronModelInfra

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

universe v₁ u₁ v₂ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}}

instance isIso_homMk {X Y : ∫ᶜ F} (e : X.base ≅ Y.base)
    (φ : X.fiber ≅ (F.map e.hom.op.toLoc).toFunctor.obj Y.fiber) : IsIso (homMk e.hom φ.hom) := by
  haveI : Mono (homMk e.hom φ.hom) := mono_homMk e.hom φ.hom
  haveI : IsSplitEpi (homMk e.hom φ.hom) := IsSplitEpi.mk' ⟨sectionMk e φ, sectionMk_comp e φ⟩
  exact isIso_of_mono_of_isSplitEpi _

end CategoryTheory.Pseudofunctor.CoGrothendieck


end
