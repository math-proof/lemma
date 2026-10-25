/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/QuotientToRayClass.lean -/

import Theorem.NumberTheory.NumberField.RayClass.IntegralUnits.Part4
import Lemma.Nat.NumberField.RayClass.IntegralUnits
import Lemma.Nat.NumberField.RayClass.PrincipalIdeal
import Lemma.Nat.NumberField.RayClass.Group
import Theorem.NumberTheory.NumberField.RayClass.PrincipalIdeal
import Def.NumberTheory.NumberField.RayClass.Group
import Def.NumberTheory.NumberField.RayClass.QuotientToRayClass.Part3
@[expose] noncomputable section

open scoped nonZeroDivisors

/-!
# Ray-element quotient to the ray class group (N406 E3)

Quotient stage of ATLAS NumberTheoryI N406, Theorem 21.8, Section 21.3:
the ray-element class map into the ray class group, its descent to the
ray-element quotient, representative rules, kernels, and exactness at the
quotient, plus the transported residue-sign corollary.

Source (immutable, ATLAS NumberTheoryI N406 at commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`):
`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`, E3 lines 1110--1118
(`exactSeq_map3`) and 1284--1342 (`exactSeq_exact_at_quotient`).

Source-to-API map:
- ATLAS `exactSeq_map3`, lines 1110--1118, to `rayElementClassMap` and
  `rayQuotientToRayClassGroup` (`QuotientGroup.lift` of the `rayClassMap` after
  `principalRayIdealMap` composite);
- ATLAS `exactSeq_exact_at_quotient`, lines 1284--1342, to
  `rayQuotientToRayClassGroup_ker` and
  `integralUnitsToRayQuotient_mulExact_rayQuotientToRayClassGroup`.
- Representation differences: ATLAS works with `UnitsCoprime`,
  `UnitsCongruent_in_UnitsCoprime`, and `QuotientUnits`; here these are
  `rayElements m`, `rayOneElements m`, and `rayElements m ⧸ rayOneElements m`.
  ATLAS valuation/subtype reconstruction (lines 1206--1282) is replaced by the
  merged E2 lemmas `rayGroup_eq_map_rayOneElements` and
  `toPrincipalIdeal_eq_iff_exists_integralUnit_mul`; the integral-unit
  principal-ideal computation (lines 1160--1175) is replayed locally as
  `principalRayIdealMap_integralUnitsToRayElements`.
- The transported `residueSignToRayClassGroup` family has no ATLAS source span;
  it is the canonical corollary across `rayElementsQuotientEquivResidueSign`.

E3 partial-stage boundary: this module stops before `exactSeq_map4`
(lines 1120--1132), exactness at the ray class group (lines 1343--1429), and
coprime representatives / surjectivity / the six-term wrapper
(lines 1431--1480). It does not reimplement E1, E2, or the quotient
equivalence. Exactness holds only at the quotient: the kernel of
`rayElementClassMap` itself can be larger than `rayOneElements` (it need not
equal `rayOneElements`: it also contains the images of integral units, which
need not lie in `rayOneElements`), so no such kernel equality is claimed.
-/


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- The transported map undoes the quotient equivalence. -/
@[simp] theorem residueSignToRayClassGroup_equiv (m : Modulus K)
    (q : rayElements m ⧸ rayOneElements m) :
    residueSignToRayClassGroup m (rayElementsQuotientEquivResidueSign m q) =
      rayQuotientToRayClassGroup m q := by
  simp [residueSignToRayClassGroup]

end Modulus
end NumberField
