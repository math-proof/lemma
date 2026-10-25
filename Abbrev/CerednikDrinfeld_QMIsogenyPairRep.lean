import Def.CerednikDrinfeld_QMIsogeny
import Structure.CerednikDrinfeld_QMRigidification

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace CerednikDrinfeld.QM.FakeEllipticCurve.IsogenyPair

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

abbrev PtFamily (r d : ℕ) {S : Type} [CommRing S] (E A : FakeEllipticCurve Λ N S)
    {X : Scheme.{0}} (ξ : X ⟶ Spec (CommRingCat.of S)) : Type 1 :=
  ∀ (T : Type) [CommRing T] [Algebra S T]
  (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
  (gA : A'.A ⟶ A.A) (_ : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
  (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f),
  FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ' → FakeEllipticCurve.PreservesLevel E' A' φ hφ →
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ξ

end CerednikDrinfeld.QM.FakeEllipticCurve.IsogenyPair
