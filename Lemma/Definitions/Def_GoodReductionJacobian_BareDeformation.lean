import Lemma.Definitions.Def_JacJ1Iface
import Lemma.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Lemma.Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian

structure BareDeformation {S : Type} [CommRing S] {Aₛ : Scheme.{0}} (fₛ : Aₛ ⟶ Spec (CommRingCat.of S))
    (Lₛ : RelativeGroupLaw S fₛ) (B : Type) [CommRing B] [Algebra B S] : Type 1 where

  A : Scheme.{0}

  f : A ⟶ Spec (CommRingCat.of B)

  L : RelativeGroupLaw B f

  comm : L.IsCommutative

  bundle : AbelianSchemePropertyBundle B f

  g : Aₛ ⟶ A

  cart : IsPullback g fₛ f (Spec.map (CommRingCat.ofHom (algebraMap B S)))

  hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t fₛ),
    (Lₛ.mul t P Q).1 ≫ g =
      (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B S)))
        ⟨P.1 ≫ g, by rw [Category.assoc, cart.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, cart.w, ← Category.assoc, Q.2]⟩).1

namespace BareDeformation

variable {S : Type} [CommRing S] {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
  {B : Type} [CommRing B] [Algebra B S]

def IsIso (D D' : BareDeformation fₛ Lₛ B) : Prop :=
  ∃ e : D.A ≅ D'.A, e.hom ≫ D'.f = D.f ∧ D.g ≫ e.hom = D'.g

def LiftsCoordinates {d : ℕ} (D : BareDeformation fₛ Lₛ B)
    (θₛ : RelativeGroupLaw.FormalCoordinates fₛ d) (θ : RelativeGroupLaw.FormalCoordinates D.f d) : Prop :=
  ∀ (B'' : Type) [CommRing B''] [Algebra B B''] [Algebra S B''] [IsScalarTower B S B''] (s : Fin d → B''),
    (∀ i, IsNilpotent (s i)) → (θₛ B'' s).1 ≫ D.g = (θ B'' s).1

end BareDeformation

end GoodReductionJacobian

end
