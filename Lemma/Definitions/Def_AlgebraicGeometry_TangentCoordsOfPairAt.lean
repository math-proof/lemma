import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Lemma.Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Lemma.Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Lemma.Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Lemma.Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Lemma.Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T')
  (C : Type u) [CommRing C] [Algebra T' C]

def chartRingHom {Ak : Scheme.{u}} (Ue : Ak.Opens)
    (w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})) :
    Γ(Ak, Ue) →+* thickening T' V C :=
  (Ue.topIso.inv ≫ w₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (thickening T' V C))).hom).hom

def IsTangentCoordsOfPairAt {Y : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Y)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (Ue : Ak.Opens)
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))) : Prop :=
  ∃ (w₀ : Spec (CommRingCat.of (thickening T' V C)) ⟶ Ak)
    (hw₀ : w₀ ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C))
    (w₁ : Spec (CommRingCat.of (thickening T' V C)) ⟶ (Ue : Scheme.{u})),
    IsTangentOfPair I V ι C u v (w₀ ≫ ak) ∧
    w₁ ≫ Ue.ι = (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
                  (thickening_isPullback V C) w₀ hw₀).1 ∧
    c = tangentCoords T' V C (chartRingHom V C Ue w₁)

end AlgebraicGeometry.SmallExtension

end
