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
import Structure.v1.Atlas.AlgebraicGeometryI.code.CanonicalDivisorDecomposition.Part2


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

attribute [instance] CurveCoveringDirect.instCR CurveCoveringDirect.instDR
  CurveCoveringDirect.instCS CurveCoveringDirect.instDS
  CurveCoveringDirect.instAlg CurveCoveringDirect.instNZ

/-- Ramification degree of a `CurveCoveringDirect`. -/
def CurveCoveringDirect.deg_R (f : CurveCoveringDirect) : ℤ :=
  globalRamification f.S f.basePrimes f.h_max f.h_bot

/-- Forgetful map from the local `CurveCovering` data to the simpler `CurveCoveringDirect`. -/
def CurveCovering.toDirect (f : CurveCovering) : CurveCoveringDirect where
  R := f.R
  S := f.S
  X := f.X
  Y := f.Y
  n := f.n
  h_n_pos := f.h_n_pos
  basePrimes := f.basePrimes
  h_max := f.h_max
  h_bot := f.h_bot
  h_degK_formula := f.degK_eq

end TrivialCovering
end GlobalRamification
end
