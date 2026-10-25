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
import Structure.StatisticalMechanics.Code.Universality.HexFiniteStripBoundary


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

variable {V : Type*} [DecidableEq V]


namespace HexFiniteStripBoundaryData

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
  {P : D.InteriorPairing} (B : HexFiniteStripBoundaryData R h0 D P)


theorem raw_eq_zero :
    hexFiniteStripRaw B.Fa B.alphaRest B.betaSum B.epsSum B.epsbarSum = 0 := by
  have hraw := D.hexBoundaryRaw P B.interior_sub
  rw [B.contour_eq] at hraw
  exact hraw


end HexFiniteStripBoundaryData
end StatMech.Universality
