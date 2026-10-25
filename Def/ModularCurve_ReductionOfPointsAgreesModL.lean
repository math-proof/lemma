import Mathlib
import Lemma.AlgebraicGeometry.NeronModelPropertyBundleCarrier
import Lemma.AlgebraicGeometry.RelativeGroupLaw
import Lemma.ModularCurve.ReductionModL

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace ModularCurve

def ReductionOfPointsAgreesModL (p : ℕ) [NeZero p]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    {R : Type} [CommRing R] {J : Scheme.{0}} (f : J ⟶ Spec (CommRingCat.of R))
    (σ : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of R))
    (ptsGen : JZero p ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom A.subtype) ≫ σ) f)
    (ptsSp : JZeroC (IsLocalRing.ResidueField ↥A) p ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ σ) f) : Prop :=
  ∀ x : JZero p, ∃ xA : SchemeHomOver σ f,
    schemeHomOverComp (Spec.map (CommRingCat.ofHom A.subtype)) rfl xA = ptsGen x ∧
    schemeHomOverComp (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))) rfl xA
      = ptsSp (reductionModL A p x)

end ModularCurve

end
