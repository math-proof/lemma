/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/ResidueSign.lean -/

import Theorem.NumberTheory.NumberField.RayClass.WeakApproximation
import Lemma.Nat.NumberField.RayClass.WeakApproximation
import Lemma.Nat.NumberField.RayClass.InfiniteSign
import Theorem.NumberTheory.NumberField.RayClass.InfiniteSign.Part4
import Theorem.NumberTheory.NumberField.RayClass.ResidueSign
@[expose] noncomputable section

open scoped nonZeroDivisors

/-!
# Combined residue-sign map and ray quotient equivalence (N406)

Quotient-isomorphism clause of ATLAS NumberTheoryI N406, Theorem 21.8, Section 21.3:
the product of the infinite-sign map and the finite-residue map on ray elements
is surjective with kernel the ray-one subgroup, so the ray-element quotient is
canonically equivalent to the residue-sign target.

Source: [`v1/Atlas/NumberTheoryI/code/RayClassFields.lean`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L2194-L2647),
declaration
[`RayClassField.theorem_21_8_quotient_iso`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L2607-L2647).
The controlled approximation is `weak_approx_coprime_sign_finitePart`
(lines 2255--2568), product surjectivity is `signTimesFinitePart_surjective`
(lines 2576--2594), and the quotient packaging is `theorem_21_8_quotient_iso`
(lines 2607--2647).

Source-to-API map:
- ATLAS `signTimesFinitePart_surjective`, lines 2576--2594, to `residueSignMap`
  and `residueSignMap_surjective`;
- the kernel computation inside `theorem_21_8_quotient_iso`, lines 2607--2643,
  to `rayOneElements`, `residueSignMap_ker`, and `residueSignMap_eq_one_iff`;
- ATLAS quotient packaging, lines 2644--2647, to
  `rayElementsQuotientEquivResidueSign`.

The six-term exact sequence at source lines 1012--1480 remains a separate later
stage; this module does not complete all of N406.
-/


namespace NumberField

namespace Modulus

variable {K : Type*} [Field K] [NumberField K]

/-- Ray-one subgroup: ray elements trivial at both coordinates. -/
def rayOneElements (m : Modulus K) : Subgroup (rayElements m) :=
  finiteRayOneElements m ⊓ positiveRayElements m

end Modulus
end NumberField
