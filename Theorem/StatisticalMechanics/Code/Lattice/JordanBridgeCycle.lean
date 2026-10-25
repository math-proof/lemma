/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanBridgeCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jbc_rot90Inv_rot90Fun (a : Site 2) : rot90Inv (rot90Fun a) = a := by
  have := rot90Equiv.left_inv a; simpa [rot90Equiv] using this


theorem jbc_rot90Fun_rot90Inv (a : Site 2) : rot90Fun (rot90Inv a) = a := by
  have := rot90Equiv.right_inv a; simpa [rot90Equiv] using this


theorem jbc_crossEdge_symm_pair (f g : Site 2) :
    crossEdge.symm s(f, g) = s(rot90Inv f, rot90Inv g) := by
  simp [crossEdge, sym2Congr]


theorem jbc_crossEdge_symm_rot (a b : Site 2) :
    crossEdge.symm s(rot90Fun a, rot90Fun b) = s(a, b) := by
  rw [jbc_crossEdge_symm_pair, jbc_rot90Inv_rot90Fun a, jbc_rot90Inv_rot90Fun b]


end Lattice
end StatMech
