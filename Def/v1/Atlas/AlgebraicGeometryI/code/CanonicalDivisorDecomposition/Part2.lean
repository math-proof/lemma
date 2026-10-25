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
import Structure.v1.Atlas.AlgebraicGeometryI.code.CanonicalDivisorDecomposition


noncomputable section

open Ideal Module CanonicalSheafCurves

section GlobalRamification

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [NoZeroSMulDivisors R S]

attribute [instance] CurveCovering.instCR CurveCovering.instDR
  CurveCovering.instCS CurveCovering.instDS CurveCovering.instAlg
  CurveCovering.instNZ

section GlobalFormula

variable (f : CurveCovering)

/-- The ramification degree `deg R` of a curve covering. -/
def CurveCovering.deg_R : ℤ :=
  globalRamification f.S f.basePrimes f.h_max f.h_bot

end GlobalFormula
end GlobalRamification
end
