import Def.CerednikDrinfeld_QMModuli

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Quaternion

namespace CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

def IsIsogenyPair (d : ℕ) (E E' : FakeEllipticCurve Λ N S) (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A) : Prop :=
  ∃ (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E.f = E'.f),
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = E'.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
    (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E'.f),
      mapPt ψ hψ (E'.L.mul t P Q) = E.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
    (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ E'.act x) ∧ (∀ x : ↥Λ, E'.act x ≫ ψ = ψ ≫ E.act x) ∧
    (∀ hd : ((d : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      φ ≫ ψ = E.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩ ∧ ψ ≫ φ = E'.act ⟨((d : ℚ) : ℍ[ℚ, a, b]), hd⟩)

def IsIsogeny (d : ℕ) (E E' : FakeEllipticCurve Λ N S) : Prop :=
  ∃ (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A), IsIsogenyPair d E E' φ ψ

def PreservesLevel (E E' : FakeEllipticCurve Λ N S) (φ : E.A ⟶ E'.A) (hφ : φ ≫ E'.f = E.f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
    FactorsThrough E.lev P → FactorsThrough E'.lev (mapPt φ hφ P)

end CerednikDrinfeld.QM.FakeEllipticCurve

end
