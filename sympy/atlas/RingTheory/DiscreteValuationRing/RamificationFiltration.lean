/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/RamificationFiltration.lean -/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Lemma.Int.RamificationInertia.Valuation
/-!
# Ramification-power identity for local DVR extensions

Prerequisite for the corrected ATLAS NumberTheoryI N261 upper different-exponent bound
(Theorem 12.27): for a torsion-free local homomorphism `A → B` of discrete valuation
rings, the extended base maximal ideal is the `e`-th power of the target maximal ideal,
where `e` is the (current unprimed) ramification index `Ideal.ramificationIdx`.

This file states only that ideal identity plus an element-membership corollary. It does
not state the different containment
`span {(e : B)} * maximalIdeal B ^ (e - 1) ≤ differentIdeal A B`, let alone N261 itself.

ATLAS source correspondence:
[`v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean` lines 1237-1324](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean#L1237-L1324).
The source's exact wild equality `different_valuation_exact` (lines 1269--1276) is
stated there without a completed proof and is false in general wild ramification;
it is not formalized here. Source-to-API map: the source's local ramification
exponent is mapped here to `IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx`,
while the upper different bound is deliberately deferred.

## Main results

* `IsDiscreteValuationRing.map_maximalIdeal_eq_pow_ramificationIdx`: the ideal identity.
* `IsDiscreteValuationRing.algebraMap_mem_maximalIdeal_pow_ramificationIdx`:
  the element-membership corollary.
-/

open IsLocalRing

namespace IsDiscreteValuationRing

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [Module.IsTorsionFree A B] [IsLocalHom (algebraMap A B)]
end IsDiscreteValuationRing
