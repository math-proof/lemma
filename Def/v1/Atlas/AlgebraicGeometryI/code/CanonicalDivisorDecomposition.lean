/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitz
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannHurwitz
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
import Mathlib.RingTheory.DedekindDomain.Different


noncomputable section

open Ideal Module CanonicalSheafCurves

section GlobalRamification

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [NoZeroSMulDivisors R S]

/-- Global ramification contribution: sum of the total ramification at each prime of `R` lying
under the cover `S/R`. -/
def globalRamification
    (basePrimes : Finset (Ideal R))
    (hmax : ∀ p ∈ basePrimes, p.IsMaximal)
    (hbot : ∀ p ∈ basePrimes, p ≠ ⊥) : ℤ :=
  basePrimes.sum fun p =>
    if h : p ∈ basePrimes then
      haveI : p.IsMaximal := hmax p h
      totalRamificationAt S p (hbot p h)
    else 0

end GlobalRamification
end
