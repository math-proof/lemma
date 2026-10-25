import Structure.JacJ1Iface
import Structure.AlgebraicGeometry_RelativeGroupLaw
import Def.AlgebraicGeometry_FormalGroupAlongSection

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


end BareDeformation

end GoodReductionJacobian

end
