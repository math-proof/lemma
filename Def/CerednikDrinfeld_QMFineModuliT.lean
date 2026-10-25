import Structure.CerednikDrinfeld_QMFineModuli
import Def.CerednikDrinfeld_QMFormalModuleOf

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace CerednikDrinfeld.QM

namespace FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def WithFullLevel.IsoVia {S : Type} [CommRing S] {n : ℕ} (u u' : WithFullLevel Λ N n S)
    (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f) : Prop :=
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt i.hom hi (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt i.hom hi P) (mapPt i.hom hi Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ i.hom = i.hom ≫ u'.1.act x) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P ↔ FactorsThrough u'.1.lev (mapPt i.hom hi P)) ∧
    mapPt i.hom hi u.2.P = u'.2.P


def WithFullLevel.IsTwistVia {S : Type} [CommRing S] {n : ℕ} (c : ↥Λ) (u u' : WithFullLevel Λ N n S)
    (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f) : Prop :=
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u'.1.act x) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P ↔ FactorsThrough u'.1.lev (mapPt e.hom he P)) ∧
    mapPt e.hom he (pushPt (u.1.act c) (u.1.act_over c) u.2.P) = u'.2.P


def WithFullLevel.IsoTVia {S : Type} [CommRing S] {n ℓ : ℕ} (u u' : WithFullLevel Λ N n S)
    (C : u.1.ExtraLevel ℓ) (C' : u'.1.ExtraLevel ℓ) (i : u.1.A ≅ u'.1.A) (hi : i.hom ≫ u'.1.f = u.1.f) : Prop :=
  WithFullLevel.IsoVia u u' i hi ∧
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough C.levK P ↔ FactorsThrough C'.levK (mapPt i.hom hi P)

end FakeEllipticCurve

end CerednikDrinfeld.QM
