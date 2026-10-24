import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Lemma.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace AlgebraicGeometry.RelPicard.LFP

open Scheme.TwoAffineOpenCover

variable (R : Type u) [CommRing R]

noncomputable def stageHom {A₀ A' : Type u} [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A']
    (f : A₀ →ₐ[R] A') : SchemeHomOver (specMap R A') (specMap R A₀) :=
  ⟨Spec.map (CommRingCat.ofHom f.toRingHom), by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    change f.toRingHom (algebraMap R A₀ x) = algebraMap R A' x
    exact f.commutes x⟩

@[simp] theorem stageHom_val {A₀ A' : Type u} [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A']
    (f : A₀ →ₐ[R] A') : (stageHom R f).1 = Spec.map (CommRingCat.ofHom f.toRingHom) := rfl

end AlgebraicGeometry.RelPicard.LFP

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))
    {A₀ A' : Type u} [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A']
    (ψ : SchemeHomOver (specMap R A') (specMap R A₀))

theorem baseChangeSnd_fst :
    RelPicard.baseChangeSnd c ψ ≫ Limits.pullback.fst c (specMap R A₀) =
      Limits.pullback.fst c (specMap R A') :=
  (Limits.pullback.lift_fst _ _ _).trans (Category.comp_id _)

theorem baseChangeSnd_preimage_U0 :
    RelPicard.baseChangeSnd c ψ ⁻¹ᵁ (𝒱.pullback c A₀).U0 = (𝒱.pullback c A').U0 := by
  rw [pullback_U0, pullback_U0, ← Scheme.Hom.comp_preimage, baseChangeSnd_fst]

theorem baseChangeSnd_preimage_U1 :
    RelPicard.baseChangeSnd c ψ ⁻¹ᵁ (𝒱.pullback c A₀).U1 = (𝒱.pullback c A').U1 := by
  rw [pullback_U1, pullback_U1, ← Scheme.Hom.comp_preimage, baseChangeSnd_fst]

theorem baseChangeSnd_preimage_inf :
    RelPicard.baseChangeSnd c ψ ⁻¹ᵁ ((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1) =
      (𝒱.pullback c A').U0 ⊓ (𝒱.pullback c A').U1 := by
  rw [Scheme.Hom.preimage_inf, baseChangeSnd_preimage_U0, baseChangeSnd_preimage_U1]

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
