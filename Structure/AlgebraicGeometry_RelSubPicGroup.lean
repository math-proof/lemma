import Mathlib
import Instance.AlgebraicGeometry_RelativePicardFunctor
import Structure.AlgebraicGeometry_RepresentsRelSubPic
import Def.AlgebraicGeometry_RelSubPicPresheaf
import Def.AlgebraicGeometry_RelativeGroupLawGrpObj
import Structure.JacJ1Iface
import Instance.SheafOfModules_Monoidal
import Instance.AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

def RigidifiedLineBundle.tensor {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (L M : RigidifiedLineBundle c ε t) : RigidifiedLineBundle c ε t where
  L := L.L ⊗ M.L
  isInvertible := L.isInvertible.tensor M.isInvertible
  rigidified := ⟨(Scheme.Modules.pullbackTensorObjIso _ _ _) ≪≫ (L.rigidified.some ⊗ᵢ M.rigidified.some) ≪≫ λ_ _⟩


structure SubPicGroupCondition (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) extends SubPicCondition c ε where
  tensor_mem : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L M : RigidifiedLineBundle c ε t),
    P t L → P t M → P t (L.tensor M)
  inv_mem : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L M : RigidifiedLineBundle c ε t),
    Nonempty ((L.tensor M).L ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L) → P t L → P t M


end AlgebraicGeometry.RelPicard

end
