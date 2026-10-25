import Mathlib
import Structure.ModularCurve_DRResolvedModelPackageV4

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme


end AlgebraicGeometry.Scheme

namespace ModularCurve.DRModelPackage

variable {p : ℕ} [Fact p.Prime] (𝔛 : DRModelPackage p)
  (O : Type) [CommRing O] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ)

abbrev baseChangeO (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] : Scheme.{0} :=
  pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))

abbrev baseChangeO.toBase (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] :
    baseChangeO p O ⟶ Spec (CommRingCat.of O) :=
  pullback.snd _ _

abbrev crossingPt (n : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ))) : ↥(baseChangeO p O) :=
  (pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base n

abbrev baseGerm (x : ↥(baseChangeO p O)) (o : O) : (baseChangeO p O).presheaf.stalk x :=
  (baseChangeO p O).presheaf.germ ⊤ x trivial
    ((baseChangeO.toBase p O).appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o))

abbrev ξinf : ↥(baseChangeO p O) :=
  letI := (𝔛.ratModel κ).isIntegral
  (𝔛.compInf κ ≫ DRModel.baseChangeMap toκ).base (genericPoint (𝔛.ratModel κ).C)

abbrev ξzero : ↥(baseChangeO p O) :=
  letI := (𝔛.ratModel κ).isIntegral
  (𝔛.compZero κ ≫ DRModel.baseChangeMap toκ).base (genericPoint (𝔛.ratModel κ).C)

end ModularCurve.DRModelPackage

end
