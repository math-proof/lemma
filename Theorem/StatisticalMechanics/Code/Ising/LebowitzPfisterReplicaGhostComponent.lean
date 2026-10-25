/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaGhostComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaAggregateSwitching
import Theorem.StatisticalMechanics.Code.Sharpness.SwitchingDichotomy.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

omit [Fintype V] [Fintype I] [DecidableEq I] in


theorem lpReplicaOffdiagSource_eq_six
    (sites : I -> V) (hsite : Function.Injective sites)
    {i j : I} (hij : i ≠ j) :
    lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1 =
      {lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        lpReplicaCurrentLeft sites i, lpReplicaCurrentRight sites i,
        lpReplicaCurrentLeft sites j, lpReplicaCurrentRight sites j} := by
  have hs : sites i ≠ sites j := hsite.ne hij
  ext z
  rcases z with (z | b)
  · rcases z with x | x <;>
      simp [lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff] <;>
      by_cases hi : x = sites i <;> by_cases hj : x = sites j <;>
        simp_all
  · cases b <;>
      simp [lpMatchingSeamSource, lpMatchingGhostSource,
        lpReplicaCurrentLeft, lpReplicaCurrentRight,
        lpReplicaCurrentGhost0, lpReplicaCurrentGhost1,
        Finset.mem_symmDiff]

end
end StatMech.Ising
