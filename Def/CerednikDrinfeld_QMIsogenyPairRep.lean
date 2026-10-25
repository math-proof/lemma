import Def.CerednikDrinfeld_QMIsogeny
import Lemma.CerednikDrinfeld.QMRigidification
import Abbrev.CerednikDrinfeld_QMIsogenyPairRep

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace CerednikDrinfeld.QM.FakeEllipticCurve.IsogenyPair

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def RepresentsOn (r d : ℕ) {S : Type} [CommRing S] (E A : FakeEllipticCurve Λ N S)
    {X : Scheme.{0}} (ξ : X ⟶ Spec (CommRingCat.of S)) (pt : PtFamily r d E A ξ) : Prop :=

      (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
          (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ)
          (E'' A'' : FakeEllipticCurve Λ N T) (gE'' : E''.A ⟶ E.A) (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E'' gE'')
          (gA'' : A''.A ⟶ A.A) (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A'' gA'')
          (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
          (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ') (hm : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ)
          (iE : E'.A ≅ E''.A) (hiE : iE.hom ≫ E''.f = E'.f) (iA : A'.A ≅ A''.A) (hiA : iA.hom ≫ A''.f = A'.f),
          FakeEllipticCurve.IsoVia E' E'' iE hiE → FakeEllipticCurve.IsoVia A' A'' iA hiA →
          iE.hom ≫ gE'' = gE → iA.hom ≫ gA'' = gA → iE.hom ≫ ψ = φ ≫ iA.hom →
            pt T E' A' gE hgE gA hgA φ φ' hφ hp hl = pt T E'' A'' gE'' hgE'' gA'' hgA'' ψ ψ' hψ hq hm) ∧

      (∀ (T T' : Type) [CommRing T] [Algebra S T] [CommRing T'] [Algebra S T'] (f : T →ₐ[S] T')
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
          (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ)
          (E'' A'' : FakeEllipticCurve Λ N T') (hE : E''.A ⟶ E'.A) (hhE : FakeEllipticCurve.IsPullbackVia (f : T →+* T') E' E'' hE)
          (hA : A''.A ⟶ A'.A) (hhA : FakeEllipticCurve.IsPullbackVia (f : T →+* T') A' A'' hA)
          (hgE'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') E E'' (hE ≫ gE))
          (hgA'' : FakeEllipticCurve.IsPullbackVia (algebraMap S T') A A'' (hA ≫ gA))
          (ψ : E''.A ⟶ A''.A) (ψ' : A''.A ⟶ E''.A) (hψ : ψ ≫ A''.f = E''.f)
          (hq : FakeEllipticCurve.IsIsogenyPair (r ^ d) E'' A'' ψ ψ') (hm : FakeEllipticCurve.PreservesLevel E'' A'' ψ hψ),
          ψ ≫ hA = hE ≫ φ → ψ' ≫ hE = hA ≫ φ' →
            (pt T' E'' A'' (hE ≫ gE) hgE'' (hA ≫ gA) hgA'' ψ ψ' hψ hq hm).1 =
              Spec.map (CommRingCat.ofHom (f : T →+* T')) ≫ (pt T E' A' gE hgE gA hgA φ φ' hφ hp hl).1) ∧

      (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S T))) ξ),
          ∃ (φ : E'.A ⟶ A'.A) (φ' : A'.A ⟶ E'.A) (hφ : φ ≫ A'.f = E'.f)
            (hp : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ φ') (hl : FakeEllipticCurve.PreservesLevel E' A' φ hφ),
            pt T E' A' gE hgE gA hgA φ φ' hφ hp hl = z) ∧

      (∀ (T : Type) [CommRing T] [Algebra S T]
          (E' A' : FakeEllipticCurve Λ N T) (gE : E'.A ⟶ E.A) (hgE : FakeEllipticCurve.IsPullbackVia (algebraMap S T) E E' gE)
          (gA : A'.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia (algebraMap S T) A A' gA)
          (φ₁ : E'.A ⟶ A'.A) (φ₁' : A'.A ⟶ E'.A) (hφ₁ : φ₁ ≫ A'.f = E'.f)
          (hp₁ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₁ φ₁') (hl₁ : FakeEllipticCurve.PreservesLevel E' A' φ₁ hφ₁)
          (φ₂ : E'.A ⟶ A'.A) (φ₂' : A'.A ⟶ E'.A) (hφ₂ : φ₂ ≫ A'.f = E'.f)
          (hp₂ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E' A' φ₂ φ₂') (hl₂ : FakeEllipticCurve.PreservesLevel E' A' φ₂ hφ₂),
          pt T E' A' gE hgE gA hgA φ₁ φ₁' hφ₁ hp₁ hl₁ = pt T E' A' gE hgE gA hgA φ₂ φ₂' hφ₂ hp₂ hl₂ → φ₁ = φ₂ ∧ φ₁' = φ₂')

end CerednikDrinfeld.QM.FakeEllipticCurve.IsogenyPair
