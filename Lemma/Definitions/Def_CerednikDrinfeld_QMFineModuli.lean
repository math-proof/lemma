import Lemma.Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Quaternion

namespace CerednikDrinfeld.QM

namespace FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def sectionAt {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f) (k : Type u) [Field k] (sk : S →+* k) :
    SchemeHomOver (geomPoint k sk) f :=
  schemeHomOverComp (geomPoint k sk) (Category.comp_id _) P

structure FullLevel {S : Type u} [CommRing S] (E : FakeEllipticCurve Λ N S) (m : ℕ) : Type u where

  P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f

  torsion : nsmulPt E.L (𝟙 (Spec (CommRingCat.of S))) m P = E.L.one (𝟙 (Spec (CommRingCat.of S)))

  generates : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (Q : SchemeHomOver (geomPoint k sk) E.f),
    nsmulPt E.L (geomPoint k sk) m Q = E.L.one (geomPoint k sk) →
      ∃ x : ↥Λ, pushPt (E.act x) (E.act_over x) (sectionAt P k sk) = Q

  annihilator : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k) (x : ↥Λ),
    pushPt (E.act x) (E.act_over x) (sectionAt P k sk) = E.L.one (geomPoint k sk) ↔
      ∃ y : ↥Λ, (x : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])

abbrev WithFullLevel (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ) (S : Type u) [CommRing S] : Type (u + 1) :=
  Σ E : FakeEllipticCurve Λ N S, E.FullLevel m

def WithFullLevel.Iso {S : Type u} [CommRing S] {m : ℕ} (u u' : WithFullLevel Λ N m S) : Prop :=
  ∃ (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u'.1.act x) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P ↔ FactorsThrough u'.1.lev (mapPt e.hom he P)) ∧
    mapPt e.hom he u.2.P = u'.2.P

def WithFullLevel.IsTwist {S : Type u} [CommRing S] {m : ℕ} (c : ↥Λ) (u u' : WithFullLevel Λ N m S) : Prop :=
  ∃ (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
    (∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u'.1.act x) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P ↔ FactorsThrough u'.1.lev (mapPt e.hom he P)) ∧
    mapPt e.hom he (pushPt (u.1.act c) (u.1.act_over c) u.2.P) = u'.2.P

def WithFullLevel.IsPullback {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') {m : ℕ}
    (u : WithFullLevel Λ N m S) (u' : WithFullLevel Λ N m S') : Prop :=
  ∃ (g : u'.1.A ⟶ u.1.A) (hg : CategoryTheory.IsPullback g u'.1.f u.1.f (Spec.map (CommRingCat.ofHom φ))),
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' u'.1.f),
      (u'.1.L.mul t' P Q).1 ≫ g =
        (u.1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
    (∀ x : ↥Λ, u'.1.act x ≫ g = g ≫ u.1.act x) ∧
    (∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S')) (P : SchemeHomOver t' u'.1.f),
      FactorsThrough u'.1.lev P → ∃ P₀ : T ⟶ u.1.C, P₀ ≫ u.1.lev = P.1 ≫ g) ∧
    (u'.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom φ) ≫ (u.2.P).1

end FakeEllipticCurve

variable {a b : ℚ}

structure IsFineModuli (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ) {B : Type} [CommRing B]
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of B))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM) : Prop where

  ptF_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u u' : FakeEllipticCurve.WithFullLevel Λ N m S), FakeEllipticCurve.WithFullLevel.Iso u u' → ptF S s u = ptF S s u'

  ptF_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of B)),
    Spec.map (CommRingCat.ofHom φ) ≫ s = s' →
    ∀ (u : FakeEllipticCurve.WithFullLevel Λ N m S) (u' : FakeEllipticCurve.WithFullLevel Λ N m S'),
    FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → (ptF S' s' u').1 = Spec.map (CommRingCat.ofHom φ) ≫ (ptF S s u).1

  ptF_surjective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)) (x : SchemeHomOver s πM),
    ∃ u : FakeEllipticCurve.WithFullLevel Λ N m S, ptF S s u = x

  ptF_injective : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u u' : FakeEllipticCurve.WithFullLevel Λ N m S), ptF S s u = ptF S s u' → FakeEllipticCurve.WithFullLevel.Iso u u'

structure IsLevelTwistAction (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N m : ℕ) {B : Type} [CommRing B]
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of B))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) : Prop where

  over_base : ∀ g : G, (ρ g).hom ≫ πM = πM

  twist : ∀ (g : G) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u u' : FakeEllipticCurve.WithFullLevel Λ N m S),
    FakeEllipticCurve.WithFullLevel.IsTwist (χ g) u u' → (ptF S s u').1 = (ptF S s u).1 ≫ (ρ g).hom

  label_one : ∃ y : ↥Λ, (χ 1 : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])

  label_mul : ∀ g g' : G,
    ∃ y : ↥Λ, (χ (g * g') : ℍ[ℚ, a, b]) - (χ g : ℍ[ℚ, a, b]) * (χ g' : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])

  label_surjective : ∀ c d : ↥Λ,
    (∃ y : ↥Λ, (c : ℍ[ℚ, a, b]) * (d : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) →
    (∃ y : ↥Λ, (d : ℍ[ℚ, a, b]) * (c : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) →
      ∃ (g : G) (y : ↥Λ), (χ g : ℍ[ℚ, a, b]) - (c : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])

  label_injective : ∀ g g' : G,
    (∃ y : ↥Λ, (χ g : ℍ[ℚ, a, b]) - (χ g' : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])) → g = g'

end CerednikDrinfeld.QM

end
