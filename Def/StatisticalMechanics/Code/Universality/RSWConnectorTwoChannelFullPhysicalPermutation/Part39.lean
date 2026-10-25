/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part38
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_bookShiftedInnerTrace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)) :
    (hypercubicLattice 2).Walk
      (rlc_dualReflect.symm (gamma.1.1 : Site 2))
      (phb_doubleDualShift (gamma'.1.2.1 : Site 2)) := by
  have hmiddleStart : (![(-z 0 - 1), z 1 - 1] : Site 2) =
      rlc_dualReflect.symm z := by
    ext i
    fin_cases i <;> simp
  have hmiddleEnd : (![(z 0 - 1), z 1 - 1] : Site 2) =
      phb_doubleDualShift z := by
    ext i
    fin_cases i <;> simp [phb_doubleDualShift]
  let middle : (hypercubicLattice 2).Walk
      (rlc_dualReflect.symm z) (phb_doubleDualShift z) :=
    (sw_horizSeg (z 1 - 1) (-z 0 - 1) (z 0 - 1)).copy
      hmiddleStart hmiddleEnd
  exact ((right.map rlc_dualReflectSymmLatticeHom).append middle).append
    (flipLeft.map rlc_doubleDualShiftLatticeHom)


end
end StatMech.Universality
