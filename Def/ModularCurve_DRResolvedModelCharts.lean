import Mathlib
import Def.ModularCurve_DRResolvedModelPackageV4
import Instance.MvPolynomial_CrossingResolutionScheme

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

noncomputable section

namespace ModularCurve

variable {p : ℕ} [Fact p.Prime]

namespace DRResolvedModelPackage

variable {𝔛 : DRModelPackage p} {O : Type} [CommRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)

def crossingPt (n : 𝔛reg.node) : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) :=
  (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv n)

end DRResolvedModelPackage

end ModularCurve

end
