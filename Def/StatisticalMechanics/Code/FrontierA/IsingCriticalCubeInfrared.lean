/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalCubeInfrared.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingPositiveCube.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalShellGreenComparison
open Filter Finset MeasureTheory Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

variable {d : Nat}


noncomputable def currentContinuityFreePairKernel
    (d : Nat) (beta : Real) (z : Site d) : Real :=
  if z = 0 then 1 else
    currentContinuityFreeTwoPoint d beta (Percolation.origin d) z


noncomputable def currentContinuityFreeBoxPairKernel
    (d n : Nat) (beta : Real) (z : Site d) : Real :=
  if z = 0 then 1 else
    currentContinuityFreeBoxTwoPoint d n beta (Percolation.origin d) z


noncomputable def currentContinuityFreePositiveCubeAverage
    (d : Nat) (beta : Real) (m : Nat) : Real :=
  finiteTorusBlockDifferenceAverage
    (currentContinuityFreePairKernel d beta) (isingPositiveCube d m)


noncomputable def currentContinuityFreeBoxPositiveCubeAverage
    (d n : Nat) (beta : Real) (m : Nat) : Real :=
  finiteTorusBlockDifferenceAverage
    (currentContinuityFreeBoxPairKernel d n beta) (isingPositiveCube d m)

end StatMech.FrontierA
