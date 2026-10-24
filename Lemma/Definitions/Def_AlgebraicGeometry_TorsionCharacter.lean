import Lemma.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace GoodReductionJacobian.RelativeGroupLaw

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

structure TorsionCharacter (L : RelativeGroupLaw S f) (n : ℕ) {R : Type u} [CommRing R]
    (ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) where

  val : ∀ (T : Type u) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver (κ ≫ ι) f), L.IsTorsionPoint (κ ≫ ι) n x → Tˣ

  val_mul : ∀ (T : Type u) [CommRing T] (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) n x) (hy : L.IsTorsionPoint (κ ≫ ι) n y)
    (hxy : L.IsTorsionPoint (κ ≫ ι) n (L.mul (κ ≫ ι) x y)),
    val T κ (L.mul (κ ≫ ι) x y) hxy = val T κ x hx * val T κ y hy

  val_natural : ∀ (T T' : Type u) [CommRing T] [CommRing T']
    (κ : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R)) (κ' : Spec (CommRingCat.of T') ⟶ Spec (CommRingCat.of R))
    (φ : T →+* T'), Spec.map (CommRingCat.ofHom φ) ≫ κ = κ' →
    ∀ (x : SchemeHomOver (κ ≫ ι) f) (hx : L.IsTorsionPoint (κ ≫ ι) n x)
      (x' : SchemeHomOver (κ' ≫ ι) f) (hx' : L.IsTorsionPoint (κ' ≫ ι) n x'),
      x'.1 = Spec.map (CommRingCat.ofHom φ) ≫ x.1 →
      val T' κ' x' hx' = Units.map (φ : T →* T') (val T κ x hx)

namespace TorsionCharacter

variable {L : RelativeGroupLaw S f} {n : ℕ} {R R' : Type u} [CommRing R] [CommRing R']
  {ι : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)} {ι' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S)}

@[ext] theorem ext {χ χ' : TorsionCharacter L n ι} (h : χ.val = χ'.val) : χ = χ' := by
  cases χ; cases χ'; cases h; rfl

end TorsionCharacter

end GoodReductionJacobian.RelativeGroupLaw

end
