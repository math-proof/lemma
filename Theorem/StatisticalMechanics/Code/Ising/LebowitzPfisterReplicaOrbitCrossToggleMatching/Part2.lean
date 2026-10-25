/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCrossToggleMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part21
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedMatching.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagDecoratedTargetBranchedSlotState_injective
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Function.Injective
      (lpReplicaOffdiagDecoratedTargetBranchedSlotState G sites i j q) := by
  intro y w h
  rcases y with y | y <;> rcases w with w | w
  · apply congrArg Sum.inl
    apply (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q).injective
    apply lpReplicaOrientedFourColorSlotState_injective
    exact congrArg Prod.snd h
  · have hbranch := congrArg Prod.fst h
    exfalso
    change false = true at hbranch
    exact Bool.false_ne_true hbranch
  · have hbranch := congrArg Prod.fst h
    exfalso
    change true = false at hbranch
    exact Bool.false_ne_true hbranch.symm
  · apply congrArg Sum.inr
    apply (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor G sites
      (lpMatchingSeamSource
        (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j)
      (lpMatchingSeamSource
          (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i ∆
        lpMatchingGhostSource
          (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
          lpReplicaCurrentGhost1) q).injective
    apply lpReplicaOrientedFourColorSlotState_injective
    exact congrArg Prod.snd h


end
end StatMech.Ising
