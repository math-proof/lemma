/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsHoleFreeBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsSingleCircuit.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TreeNoSepEuler.Part6
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

attribute [local instance] Classical.propDecidable


def phb_doubleDualShift (x : Site 2) : Site 2 := ![x 0 - 1, x 1 - 1]


def phb_doubleDualEquiv : Site 2 ≃ Site 2 where
  toFun := phb_doubleDualShift
  invFun x := ![x 0 + 1, x 1 + 1]
  left_inv x := by
    funext i
    fin_cases i <;> simp [phb_doubleDualShift]
  right_inv x := by
    funext i
    fin_cases i <;> simp [phb_doubleDualShift]

end Lattice
end StatMech
