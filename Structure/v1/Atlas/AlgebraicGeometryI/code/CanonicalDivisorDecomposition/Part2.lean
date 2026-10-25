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
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalDivisorDecomposition.Part3


noncomputable section

open Ideal Module CanonicalSheafCurves

section GlobalRamification

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [NoZeroSMulDivisors R S]

attribute [instance] CurveCovering.instCR CurveCovering.instDR
  CurveCovering.instCS CurveCovering.instDS CurveCovering.instAlg
  CurveCovering.instNZ

section TrivialCovering

open CanonicalSheafCurves

/-- Simplified curve-covering structure: stores only the global canonical-degree formula
without local data. -/
structure CurveCoveringDirect where
  R : Type*
  S : Type*
  [instCR : CommRing R]
  [instDR : IsDedekindDomain R]
  [instCS : CommRing S]
  [instDS : IsDedekindDomain S]
  [instAlg : Algebra R S]
  [instNZ : NoZeroSMulDivisors R S]
  X : SmoothCompleteCurve
  Y : SmoothCompleteCurve
  n : ℤ
  h_n_pos : 0 < n
  basePrimes : Finset (Ideal R)
  h_max : ∀ p ∈ basePrimes, p.IsMaximal
  h_bot : ∀ p ∈ basePrimes, p ≠ ⊥
  h_degK_formula :
    X.degK = n * Y.degK + globalRamification S basePrimes h_max h_bot

end TrivialCovering
end GlobalRamification
end
