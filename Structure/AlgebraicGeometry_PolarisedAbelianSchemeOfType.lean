import Structure.AlgebraicGeometry_FramedPolarisedAbelianScheme
import Def.AlgebraicGeometry_PolarisationRosati

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry

namespace Scheme.Modules


end Scheme.Modules

namespace Polarisation

variable {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)


end Polarisation

namespace PolarisedAbelianScheme


variable {g d n : ℕ}


structure Satisfying (g d n : ℕ) (Q : ∀ (S : Type u) [CommRing S], PolarisedAbelianScheme g d n S → Prop)
    (S : Type u) [CommRing S] where

  val : PolarisedAbelianScheme g d n S

  prop : Q S val

namespace Satisfying

variable {Q : ∀ (S : Type u) [CommRing S], PolarisedAbelianScheme g d n S → Prop}


def IsPullback {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    (X : Satisfying g d n Q S) (X' : Satisfying g d n Q S') : Prop :=
  PolarisedAbelianScheme.IsPullback φ X.val X'.val

structure IsFineModuli (g d n : ℕ) (Q : ∀ (S : Type) [CommRing S], PolarisedAbelianScheme g d n S → Prop)
    {B : Type} [CommRing B] (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      Satisfying g d n Q S → SchemeHomOver s πM) : Prop where

  pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (X X' : Satisfying g d n Q S), Iso X X' → pt S s X = pt S s X'

  pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (X : Satisfying g d n Q S) (X' : Satisfying g d n Q S'),
    IsPullback φ X X' → (pt S' s' X').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s X).1

  pt_surjective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (x : SchemeHomOver s πM),
    ∃ X : Satisfying g d n Q S, pt S s X = x

  pt_injective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (X X' : Satisfying g d n Q S), pt S s X = pt S s X' → Iso X X'

end Satisfying


end PolarisedAbelianScheme

end AlgebraicGeometry

end
