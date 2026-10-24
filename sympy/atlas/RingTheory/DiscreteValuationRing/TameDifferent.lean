/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/TameDifferent.lean -/

/-
Author: Muse Code powered by Meta Muse Spark (Muse Spark 1.3)
-/

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import sympy.atlas.RingTheory.DiscreteValuationRing.MaximalIdealPowQuotientTrace
import Lemma.Int.DiscreteValuationRing.MaximalIdealPowQuotientTrace
/-!
# Tame different-ideal equality for DVR extensions

Let `A → B` be a finite torsion-free extension of discrete valuation rings with
separable fraction-field extension and separable residue-field extension. When
`Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ e` with
`IsUnit (e : B)` (the tame hypothesis), the different ideal is exactly the
`(e - 1)`-st power of the target maximal ideal:

`differentIdeal A B = maximalIdeal B ^ (e - 1)`.

The lower bound `maximalIdeal B ^ (e - 1) ∣ differentIdeal A B` is Mathlib's
`pow_sub_one_dvd_differentIdeal`. The upper bound uses the tame
integral-trace surjectivity
`intTrace_surjective_of_isUnit_natCast_of_map_maximalIdeal_eq_pow` together
with Mathlib's `not_dvd_differentIdeal_of_intTrace_not_mem` to force the
different-ideal exponent strictly below `e`, inside the DVR ideal lattice.

ATLAS item: NumberTheoryI N261. This module is a partial stage toward the
full N261 target, not the full target itself.

ATLAS source: [`v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean`, lines
1237--1324, at revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean#L1237-L1324).
Those lines define the ramification/different valuations and state the target
bounds. This file proves the correct tame equality only. It does not prove the
false wild equality `different_valuation_exact` stated without proof at ATLAS
lines 1269--1276, which fails in general wild ramification.

Source-to-API map: the tame equality proved here,
`differentIdeal_eq_maximalIdeal_pow_sub_one_of_isUnit_natCast`, combines the
Mathlib different-ideal bounds above with the tame trace-surjectivity input
from `MathlibExt.RingTheory.DiscreteValuationRing.MaximalIdealPowQuotientTrace`;
it is not itself an ATLAS source theorem statement.

## Main results

* `differentIdeal_eq_maximalIdeal_pow_sub_one_of_isUnit_natCast`: under
  `map 𝔪A = 𝔪B ^ e` with `IsUnit (e : B)`, `differentIdeal A B =
  maximalIdeal B ^ (e - 1)`. This is the tame case only, not the false wild
  equality in ATLAS.
-/

open IsLocalRing
open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

variable (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]
  [Module.IsTorsionFree A B] [Module.Finite A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
