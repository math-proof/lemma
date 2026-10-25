/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialCellularRibbonDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialRibbonBoundaryParity.Part3
import Structure.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality


namespace StatMech.FrontierA

open Finset Equiv

open scoped BigOperators symmDiff

variable {D E K : Type*} [Fintype D] [DecidableEq D]
  [Fintype E] [DecidableEq E]


namespace CellularRibbonDualData

variable {R : RibbonPermutationSystem E D}

omit [DecidableEq E] in


theorem eulerBaseParity (C : CellularRibbonDualData R) :
    (Fintype.card E + permCycleCount R.rotation) % 2 =
      C.dualVertexCount % 2 := by
  rw [C.rotationCycles_eq_primalVertexCount]
  have h := C.cellularEuler
  omega


theorem boundaryParity (C : CellularRibbonDualData R) :
    forall F : Finset E,
      (Fᶜ.card + R.boundaryComponents F) % 2 =
        C.dualVertexCount % 2 :=
  R.boundaryParity_eq_dualVertexCount C.dualVertexCount C.eulerBaseParity

end CellularRibbonDualData
end StatMech.FrontierA
