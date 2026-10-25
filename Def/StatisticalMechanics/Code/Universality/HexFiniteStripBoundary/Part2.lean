/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexContourDefs.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripBoundary


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

variable {V : Type*} [DecidableEq V]


namespace HexFiniteStripBoundaryData

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
  {P : D.InteriorPairing} (B : HexFiniteStripBoundaryData R h0 D P)


noncomputable def toFObsBoundaryData :
    HexFObsBoundaryData where
  lam := B.lam
  ups := B.ups
  tau := B.tau
  Fa := B.Fa
  alphaRest := B.alphaRest
  alphaRest_eq := B.alphaRest_eq
  betaSum := B.betaSum
  betaSum_eq := B.betaSum_eq
  epsSum := B.epsSum
  epsSum_eq := B.epsSum_eq
  epsbarSum := B.epsbarSum
  epsbarSum_eq := B.epsbarSum_eq
  raw := by
    change hexFiniteStripRaw B.Fa B.alphaRest B.betaSum B.epsSum B.epsbarSum = 0
    exact B.raw_eq_zero


end HexFiniteStripBoundaryData
end StatMech.Universality
