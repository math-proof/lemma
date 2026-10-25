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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part37
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_bookShiftedOuterCoreTrace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1) :
    (hypercubicLattice 2).Walk
      (rlc_dualReflect.symm (gamma.1.2.1 : Site 2))
      (rlc_dualReflect.symm (gamma'.1.1 : Site 2)) := by
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hzWR : z ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).2 hzRight
  have hzWL : rlc_flipX z ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX z)).2 hzLeft
  let rightOuter := WR.dropUntil z hzWR
  let leftOuter := WL.takeUntil (rlc_flipX z) hzWL
  have hmiddleStart : (![(-z 0 - 1), z 1 - 1] : Site 2) =
      rlc_dualReflect.symm z := by
    ext i
    fin_cases i <;> simp
  have hmiddleEnd : (![(z 0 - 1), z 1 - 1] : Site 2) =
      rlc_dualReflect.symm (rlc_flipX z) := by
    ext i
    fin_cases i <;> simp [rlc_flipX, rlc_flipXFun]
  let middle : (hypercubicLattice 2).Walk
      (rlc_dualReflect.symm z)
      (rlc_dualReflect.symm (rlc_flipX z)) :=
    (sw_horizSeg (z 1 - 1) (-z 0 - 1) (z 0 - 1)).copy
      hmiddleStart hmiddleEnd
  exact (((rightOuter.map rlc_dualReflectSymmLatticeHom).reverse.append
    middle).append (leftOuter.map rlc_dualReflectSymmLatticeHom).reverse)


noncomputable def rlc_bookShiftedOuterTrace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1) :
    (hypercubicLattice 2).Walk
      (rlc_dualReflect.symm (gamma.1.2.1 : Site 2))
      ![2 * n, (rlc_dualReflect.symm (gamma'.1.1 : Site 2)) 1] := by
  let core := rlc_bookShiftedOuterCoreTrace gamma gamma' hzRight hzLeft
  let q : Site 2 := rlc_dualReflect.symm (gamma'.1.1 : Site 2)
  have hqCoord : (![q 0, q 1] : Site 2) = q := by
    ext i
    fin_cases i <;> simp
  let extension : (hypercubicLattice 2).Walk q ![2 * n, q 1] :=
    (sw_horizSeg (q 1) (q 0) (2 * n)).copy hqCoord rfl
  exact core.append extension


end
end StatMech.Universality
