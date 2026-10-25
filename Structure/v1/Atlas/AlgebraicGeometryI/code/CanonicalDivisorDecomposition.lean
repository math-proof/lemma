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
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalDivisorDecomposition


noncomputable section

open Ideal Module CanonicalSheafCurves

section GlobalRamification

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [NoZeroSMulDivisors R S]

/-- Data of a finite covering of smooth complete curves `X → Y` arising from a Dedekind ring
extension `R ⊂ S`, together with the local canonical-degree decompositions used in the
Riemann–Hurwitz formula. -/
structure CurveCovering where
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
  localDegK_X : Ideal R → ℤ
  localDegK_Y : Ideal R → ℤ
  h_degK_X_sum : X.degK = basePrimes.sum localDegK_X
  h_degK_Y_sum : Y.degK = basePrimes.sum localDegK_Y
  h_local_degree : ∀ p ∈ basePrimes,
    localDegK_X p = n * localDegK_Y p +
      (if h : p ∈ basePrimes then
        haveI : p.IsMaximal := h_max p h
        totalRamificationAt S p (h_bot p h)
      else 0)

end GlobalRamification
end
