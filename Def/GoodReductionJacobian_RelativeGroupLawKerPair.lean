module
public import Mathlib
public import Abbrev.GoodReductionJacobian_RelativeGroupLawBaseChange
public import Instance.GoodReductionJacobian_RelativeGroupLawKerPair
set_option autoImplicit false


public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra Scheme

namespace GoodReductionJacobian
namespace RelativeGroupLaw

section IsHom

variable {R : Type u} [CommRing R] {A A' A'' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)} {f'' : A'' ⟶ Spec (CommRingCat.of R)}

def IsHom (G : RelativeGroupLaw R f) (G' : RelativeGroupLaw R f') (ψ : SchemeHomOver f f') : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (G.mul t x y) ψ =
      G'.mul t (NeronModelInfra.schemeHomOverComp x ψ) (NeronModelInfra.schemeHomOverComp y ψ)


end IsHom

section KerPair

variable {R : Type u} [CommRing R] {A A' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}

abbrev kerPair (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f') : Scheme.{u} :=
  pullback (pullback.fst (φ 0).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1)
    (pullback.fst (φ 1).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1)

abbrev kerPairι (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f') : kerPair G' φ ⟶ A :=
  pullback.fst (pullback.fst (φ 0).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1)
      (pullback.fst (φ 1).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫
    pullback.fst (φ 0).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1

abbrev kerPairStr (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f') :
    kerPair G' φ ⟶ Spec (CommRingCat.of R) :=
  kerPairι G' φ ≫ f

variable (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f')

def kerPairLift {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f)
    (hx : ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one t) : T ⟶ kerPair G' φ :=
  pullback.lift
    (pullback.lift x.1 t (by rw [← one_coe_eq]; exact congrArg Subtype.val (hx 0)))
    (pullback.lift x.1 t (by rw [← one_coe_eq]; exact congrArg Subtype.val (hx 1)))
    (by rw [pullback.lift_fst, pullback.lift_fst])

def kerPairPointEquiv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver t (kerPairStr G' φ) ≃
      {x : SchemeHomOver t f // ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one t} where
  toFun z := ⟨⟨z.1 ≫ kerPairι G' φ, by rw [Category.assoc]; exact z.2⟩, kerPairι_mem G' φ z⟩
  invFun x := ⟨kerPairLift G' φ x.1 x.2, by
    show _ ≫ kerPairι G' φ ≫ f = t
    rw [← Category.assoc, kerPairLift_ι]; exact x.1.2⟩
  left_inv z := by
    have hz : z.1 ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ f = t := by
      have := z.2; simp only [Category.assoc] at this; exact this
    apply Subtype.ext
    show kerPairLift G' φ ⟨z.1 ≫ kerPairι G' φ, by rw [Category.assoc]; exact z.2⟩ (kerPairι_mem G' φ z) = z.1
    apply pullback.hom_ext
    · rw [kerPairLift, pullback.lift_fst]
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        show z.1 ≫ kerPairι G' φ = (z.1 ≫ pullback.fst _ _) ≫ pullback.fst _ _
        rw [Category.assoc]
      · rw [pullback.lift_snd, kerLeg_snd_eq, Category.assoc, hz]
    · rw [kerPairLift, pullback.lift_snd]
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        show z.1 ≫ kerPairι G' φ = (z.1 ≫ pullback.snd _ _) ≫ pullback.fst _ _
        rw [Category.assoc, kerPair_snd_fst]
      · rw [pullback.lift_snd, kerLeg_snd_eq, Category.assoc, kerPair_snd_fst_assoc, hz]
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact kerPairLift_ι G' φ x.1 x.2

abbrev kerPairιOver : SchemeHomOver (kerPairStr G' φ) f :=
  ⟨kerPairι G' φ, rfl⟩

end KerPair

section KerPairLaw

variable {R : Type u} [CommRing R] {A A' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
variable (G : RelativeGroupLaw R f) (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f')
  (hφ : ∀ i, IsHom G G' (φ i))

section

variable {G G' φ}
include hφ

end

def kerPairLaw : RelativeGroupLaw R (kerPairStr G' φ) where
  mul t z w := (kerPairPointEquiv G' φ t).symm
    ⟨G.mul t (kerPairPointEquiv G' φ t z).1 (kerPairPointEquiv G' φ t w).1,
      kerPair_mul_mem hφ t (kerPairPointEquiv G' φ t z).2 (kerPairPointEquiv G' φ t w).2⟩
  one t := (kerPairPointEquiv G' φ t).symm ⟨G.one t, kerPair_one_mem hφ t⟩
  inv t z := (kerPairPointEquiv G' φ t).symm
    ⟨G.inv t (kerPairPointEquiv G' φ t z).1, kerPair_inv_mem hφ t (kerPairPointEquiv G' φ t z).2⟩
  mul_assoc t x y z := by
    simp only [Equiv.apply_symm_apply, G.mul_assoc]
  one_mul t x := by
    simp only [Equiv.apply_symm_apply, G.one_mul, Subtype.coe_eta, Equiv.symm_apply_apply]
  mul_one t x := by
    simp only [Equiv.apply_symm_apply, G.mul_one, Subtype.coe_eta, Equiv.symm_apply_apply]
  inv_mul_cancel t x := by
    simp only [Equiv.apply_symm_apply, G.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply kerPairPoint_ext
    rw [schemeHomOverComp_coe, Category.assoc, kerPairPointEquiv_symm_apply_coe, kerPairPointEquiv_symm_apply_coe]
    have h := congrArg Subtype.val (G.mul_natural t t' ψ hψ (kerPairPointEquiv G' φ t x).1 (kerPairPointEquiv G' φ t y).1)
    rw [schemeHomOverComp_coe] at h
    rw [h, ← kerPairPointEquiv_natural, ← kerPairPointEquiv_natural]

end KerPairLaw

section Properties

variable {R : Type u} [CommRing R] {A A' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
variable (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f')

end Properties

end RelativeGroupLaw
end GoodReductionJacobian

end
