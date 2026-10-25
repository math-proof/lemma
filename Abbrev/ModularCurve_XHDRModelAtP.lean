import Mathlib
import Instance.ModularCurve_XHDifferentialsModL
import Def.ModularCurve_XHOperators
import Abbrev.ModularCurve_IgusaScheme
import Instance.AlgebraicCurve_TwoChartIntegralModel
import Structure.AlgebraicCurve_CurveModel
import Structure.AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open scoped MatrixGroups

namespace ModularCurve

namespace XHDRLevel

abbrev R (p : ℕ) : Type := ↥(GaloisRep.ratLocalizedAt p)


abbrev fibre {κ : Type} [CommRing κ] (toκ : R p →+* κ) : Scheme.{0} :=
  pullback (toBase p Γ hj) (Spec.map (CommRingCat.ofHom toκ))


end XHDRLevel

open XHDRLevel

section

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))

abbrev XHDRLevel.ΓN : Subgroup SL(2, ℤ) := CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)

abbrev XHDRLevel.ΓM : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H


end

namespace XHDRModelAtP

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)

abbrev placeOn0 (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) : Place (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) :=
  qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p (𝔛.nodeEquiv A hA ρ hρ n : ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p))

abbrev placeOn1 (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1))) : Place (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)) :=
  (𝔛.nodeEquiv A hA ρ hρ n : ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p))


end XHDRModelAtP

end ModularCurve

end
