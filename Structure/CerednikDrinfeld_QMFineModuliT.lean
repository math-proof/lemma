import Structure.CerednikDrinfeld_QMFineModuli
import Structure.CerednikDrinfeld_QMFormalModuleOf
import Def.CerednikDrinfeld_QMFineModuliT

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace CerednikDrinfeld.QM

namespace FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}


end FakeEllipticCurve

variable {a b : ℚ}

structure IsFineModuliT (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N n ℓ : ℕ) {B : Type} [CommRing B]
    (Mℓ : Scheme.{0}) (πMℓ : Mℓ ⟶ Spec (CommRingCat.of B))
    (ptFℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (u : FakeEllipticCurve.WithFullLevel Λ N n S), u.1.ExtraLevel ℓ → SchemeHomOver s πMℓ) : Prop where

  ptFℓ_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u u' : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ) (C' : u'.1.ExtraLevel ℓ)
    (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f),
    FakeEllipticCurve.WithFullLevel.IsoTVia u u' C C' i hi → ptFℓ S s u C = ptFℓ S s u' C'

  ptFℓ_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (u : FakeEllipticCurve.WithFullLevel Λ N n S) (u' : FakeEllipticCurve.WithFullLevel Λ N n S')
      (C : u.1.ExtraLevel ℓ) (C' : u'.1.ExtraLevel ℓ) (g : u'.1.A ⟶ u.1.A),
      FakeEllipticCurve.IsPullbackVia φ u.1 u'.1 g →
      (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1 →
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t u'.1.f),
        FactorsThrough C'.levK P → ∃ P₀ : T ⟶ C.K, P₀ ≫ C.levK = P.1 ≫ g) →
        (ptFℓ S' s' u' C').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptFℓ S s u C).1

  ptFℓ_surjective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (x : SchemeHomOver s πMℓ),
    ∃ (u : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ), ptFℓ S s u C = x

  ptFℓ_injective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u u' : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel ℓ) (C' : u'.1.ExtraLevel ℓ),
    ptFℓ S s u C = ptFℓ S s u' C' →
      ∃ (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f), FakeEllipticCurve.WithFullLevel.IsoTVia u u' C C' i hi

end CerednikDrinfeld.QM
