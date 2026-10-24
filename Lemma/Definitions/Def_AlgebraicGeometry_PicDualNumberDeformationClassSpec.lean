import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_RigKerDualNumber
import Lemma.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Lemma.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

namespace AlgebraicGeometry.RelPicard

section Thickening

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))

abbrev dualNumberThickening :
    HomOver (IsScalarTower.toAlgHom R A (DualNumber A)).toRingHom (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒱.pullback c (DualNumber A)) (pullback.snd c (specMap R (DualNumber A))) :=
  HomOver.stage 𝒱 c (IsScalarTower.toAlgHom R A (DualNumber A))

def oneAddEpsMul (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01 :=
  1 + algebraMap (DualNumber A) _ DualNumber.eps * (dualNumberThickening A 𝒱 c).map01 f

end Thickening

section Spec

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
variable (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
variable (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

abbrev H1StructureSheaf : Type u :=
  ((𝒱.pullback c A).structureSheafSections (pullback.snd c (specMap R A))).H1

def IsDeformationClassMap (δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱) : Prop :=
  ∀ (M : RigKerDualNumber.Carrier c ε A)
    (e₀ : Γ(M.1.L, (𝒱.pullback c (DualNumber A)).U0)) (e₁ : Γ(M.1.L, (𝒱.pullback c (DualNumber A)).U1))
    (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01),
    Scheme.Modules.IsFrameOn e₀ (𝒱.pullback c (DualNumber A)).U0 →
    Scheme.Modules.IsFrameOn e₁ (𝒱.pullback c (DualNumber A)).U1 →
    M.1.L.presheaf.map (homOfLE inf_le_right).op e₁ =
      (show Γ(Limits.pullback c (specMap R (DualNumber A)),
              (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1)
          from oneAddEpsMul A 𝒱 c f) •
        M.1.L.presheaf.map (homOfLE inf_le_left).op e₀ →
    δ (Quotient.mk _ M) = Submodule.Quotient.mk f

end Spec

end AlgebraicGeometry.RelPicard

end
