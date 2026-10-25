/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialCellularRibbonDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialRibbonBoundaryParity.Part3


namespace StatMech.FrontierA

open Finset Equiv

open scoped BigOperators symmDiff

variable {D E K : Type*} [Fintype D] [DecidableEq D]
  [Fintype E] [DecidableEq E]


structure CellularRibbonDualData (R : RibbonPermutationSystem E D) where
  primalVertexCount : Nat
  dualVertexCount : Nat
  genus : Nat
  rotationCycles_eq_primalVertexCount :
    permCycleCount R.rotation = primalVertexCount
  cellularEuler :
    primalVertexCount + dualVertexCount + 2 * genus =
      Fintype.card E + 2

end StatMech.FrontierA
