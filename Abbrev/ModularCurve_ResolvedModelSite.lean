import Mathlib
import Abbrev.AlgebraicGeometry_ResolvedModelGlueComponents
import Structure.ModularCurve_DRResolvedModelPackageV4
import Abbrev.ModularCurve_DRModelPackage
import Instance.MvPolynomial_CrossingResolutionScheme
import Instance.MvPolynomial_CrossingResolutionFibrePoints
import Structure.ModularCurve_ResolvedModelSite

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace V3Glue.SiteAux

end V3Glue.SiteAux

end

noncomputable section

namespace V3Glue.Site

open ModularCurve MvPolynomial MvPolynomial.CrossingQuotient

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O]
  (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]


variable (bc : pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ⟶ XO p O)

variable {p O κ} in


end V3Glue.Site

end

noncomputable section

namespace V3Asm

open ModularCurve MvPolynomial MvPolynomial.CrossingQuotient

variable (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (O : Type) [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)

abbrev πX : V3Glue.Site.XO p O ⟶ Spec (CommRingCat.of O) := pullback.snd _ _

abbrev bc : pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ⟶ V3Glue.Site.XO p O :=
  DRModel.baseChangeMap toκ

end V3Asm

end
