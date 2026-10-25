/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/IntegralUnits.lean -/

import Theorem.NumberTheory.NumberField.RayClass.ResidueSign.Part3
import Lemma.Nat.NumberField.RayClass.ResidueSign
import Mathlib.Algebra.Exact.Basic
import Def.NumberTheory.NumberField.RayClass.IntegralUnits.Part3
@[expose] noncomputable section

/-!
# Integral units into ray elements and exactness at units (N406 E1)

Left endpoint of the six-term exact sequence in ATLAS NumberTheoryI N406,
Theorem 21.8, Section 21.3: the integral-unit embedding, the ray-one unit
subgroup, the quotient and residue-sign endpoint maps, and exactness at units.

Source: `v1/Atlas/NumberTheoryI/code/RayClassFields.lean`,
declarations `exactSeq_map1`, `okUnitsToKUnits`, `valuation_algebraMap_unit_eq_one`,
`okUnitsInUnitsCoprime`, `okUnitsToUnitsCoprime`, `exactSeq_map2` (source lines
1012--1052) and `exactSeq_exact_at_units` (source lines 1134--1158).

Source-to-API map:
- ATLAS `UnitsCoprime` is `rayElements m`; ATLAS `UnitsCongruent_in_UnitsCoprime`
  is `rayOneElements m`; ATLAS `QuotientUnits` is the direct quotient
  `rayElements m ⧸ rayOneElements m`; ATLAS `SignsTimesUnits` is
  `ResidueSignTarget m` via `rayElementsQuotientEquivResidueSign` (PR #1367).
- ATLAS `exactSeq_map1` is `integralRayOneUnitsInclusion m`;
  `okUnitsToKUnits` is `integralUnitsToFieldUnits`;
  `valuation_algebraMap_unit_eq_one` is discharged inline in
  `integralUnitsToRayElements m` by Mathlib's
  `IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem`;
  `okUnitsToUnitsCoprime` is `integralUnitsToRayElements m`;
  `exactSeq_map2` is `integralUnitsToRayQuotient m`.
- ATLAS `exactSeq_exact_at_units` is `integralUnits_mulExact_quotient`;
  `integralUnits_mulExact_residueSign` is the transported residue-sign form used
  by the concrete six-term sequence.

E1 partial-stage boundary: this module stops before the principal-ideal material
at source line 1054 and before the integral-unit/principal-ideal bridge at line
1160. It does not add the map to the ray class group or later exactness stages.
-/


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- The quotient map evaluated on an integral unit. -/
@[simp] theorem integralUnitsToRayQuotient_apply (m : Modulus K) (u : (𝓞 K)ˣ) :
    integralUnitsToRayQuotient m u =
      QuotientGroup.mk (integralUnitsToRayElements m u) := by
  simp [integralUnitsToRayQuotient]

end Modulus
end NumberField
