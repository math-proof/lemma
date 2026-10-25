/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/RayClassToClassGroup.lean -/

import Theorem.NumberTheory.NumberField.RayClass.QuotientToRayClass.Part3
import Lemma.Nat.NumberField.RayClass.QuotientToRayClass
import Mathlib.Algebra.Exact.Basic
import Def.NumberTheory.NumberField.RayClass.RayClassToClassGroup.Part2
@[expose] noncomputable section

open scoped nonZeroDivisors

/-!
# Ray-class-to-ordinary-class-group projection (N406 E4)

Exactness stage of ATLAS NumberTheoryI N406, Theorem 21.8, Section 21.3:
the ideal-class map on coprime fractional ideals, its descent to the ray
class group, representative rules, the kernel, and exactness at the ray
class group in raw quotient and residue-sign forms.

Source (immutable, ATLAS NumberTheoryI N406 at commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`):
`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`, E4 lines 1120--1132
(`exactSeq_map4`) and 1343--1429 (`exactSeq_exact_at_ray_class`).

Source-to-API map:
- ATLAS `exactSeq_map4`, lines 1120--1132, to `coprimeIdealClassMap` and
  `rayClassToClassGroup` (`QuotientGroup.lift` of `ClassGroup.mk K` after the
  subgroup inclusion);
- ATLAS `exactSeq_exact_at_ray_class`, lines 1343--1429, to
  `rayClassToClassGroup_ker` and
  `rayQuotientToRayClassGroup_mulExact_rayClassToClassGroup`.
- Representation differences: ATLAS works with `FracIdealsCoprime_subgroup`,
  `RayGroup`, and `RayClassGroup` over explicitly coprime subtypes; here these
  are `coprimeFractionalIdeals m`, `rayGroup m`, and `RayClassGroup m`.
  ATLAS lift well-definedness (lines 1124--1132) is discharged via the merged
  E2 lemma `rayGroup_eq_map_rayOneElements` plus `principalRayIdealMap_apply`;
  principal-ideal computations use `principalRayIdealMap_apply`.
  ATLAS reverse exactness (lines 1373--1429) chooses a coprime representative
  via `rayClassMap_surjective`, obtains a principal generator via
  `ClassGroup.mk_eq_one_iff` and `FractionalIdeal.isPrincipal_iff`, proves
  `a ≠ 0`, forms `Units.mk0 a`, and lands in `rayElements m` through the
  definitional `mem_rayElements_iff` comap criterion; the source's valuation
  reconstruction (the analogue of lines 1206--1247) is obsolete and not ported.
- The transported `residueSignToRayClassGroup` corollary has no ATLAS source
  span; it crosses `rayElementsQuotientEquivResidueSign` using E3's
  transported map and its range.

E4 partial-stage boundary: this module stops before projection surjectivity
(source lines 1431--1480, E5, which needs coprime ideal-class representatives)
and before the final six-term wrapper (E5). It does not reimplement E1--E3.
-/


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- The projection evaluated on a class representative. -/
@[simp] theorem rayClassToClassGroup_rayClassMap (m : Modulus K)
    (I : coprimeFractionalIdeals m) :
    rayClassToClassGroup m (rayClassMap m I) = coprimeIdealClassMap m I := by
  simp [rayClassToClassGroup, rayClassMap]

end Modulus
end NumberField
