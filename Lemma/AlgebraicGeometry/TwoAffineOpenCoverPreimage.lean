import Lemma.AlgebraicGeometry.TwoAffineOpenCoverH1BaseChange
import Def.AlgebraicGeometry_TwoAffineOpenCoverPreimage

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable {X Y : Scheme.{u}}


@[simp] theorem preimage_U0 (𝒱 : X.TwoAffineOpenCover) (g : Y ⟶ X) [IsAffineHom g] :
    (𝒱.preimage g).U0 = g ⁻¹ᵁ 𝒱.U0 := rfl

@[simp] theorem preimage_U1 (𝒱 : X.TwoAffineOpenCover) (g : Y ⟶ X) [IsAffineHom g] :
    (𝒱.preimage g).U1 = g ⁻¹ᵁ 𝒱.U1 := rfl

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S]

theorem pullback_eq_preimage (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] :
    𝒱.pullback c A =
      @preimage _ _ 𝒱 (Limits.pullback.fst c (specMap R A)) (isAffineHom_fst c A) := rfl


@[simp] theorem HomOver.ofPreimage_hom {τ : R →+* S} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (c' : Y ⟶ Spec (.of S)) (g : Y ⟶ X) [IsAffineHom g]
    (hg : g ≫ c = c' ≫ Spec.map (CommRingCat.ofHom τ)) :
    (HomOver.ofPreimage 𝒱 c c' g hg).hom = g := rfl


theorem HomOver.pullback_hom {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ Spec (.of R)} {𝒲 : Y.TwoAffineOpenCover}
    {c' : Y ⟶ Spec (.of R)} (f : HomOver (RingHom.id R) 𝒱 c 𝒲 c') (A : Type u) [CommRing A] [Algebra R A] :
    (f.pullback A).hom ≫ Limits.pullback.fst c (specMap R A) = Limits.pullback.fst c' (specMap R A) ≫ f.hom :=
  Limits.pullback.lift_fst _ _ _

theorem HomOver.pullback_hom_comp_stage_hom {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ Spec (.of R)}
    {𝒲 : Y.TwoAffineOpenCover} {c' : Y ⟶ Spec (.of R)} (f : HomOver (RingHom.id R) 𝒱 c 𝒲 c')
    {A : Type u} [CommRing A] [Algebra R A] {B : Type u} [CommRing B] [Algebra R B] (g : A →ₐ[R] B) :
    (f.pullback B).hom ≫ (HomOver.stage 𝒱 c g).hom = (HomOver.stage 𝒲 c' g).hom ≫ (f.pullback A).hom := by
  apply Limits.pullback.hom_ext <;>
    simp only [HomOver.pullback, HomOver.stage, RelPicard.baseChangeSnd, Category.assoc, Limits.pullback.lift_fst,
      Limits.pullback.lift_fst_assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc, Category.comp_id,
      Category.id_comp]

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
