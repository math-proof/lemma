/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSameProfileCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSecondTransfer.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaSameProfileCounterexample.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.RandomCurrent


theorem not_lpReplicaSameProfileTwoBranchSelectorPrinciple :
    ¬ LPReplicaSameProfileTwoBranchSelectorPrinciple := by
  intro h
  exact lpReplicaSameProfileCounter_no_target_selector
    (h lpReplicaSameProfileCounterEnds
      lpReplicaSameProfileCounterSi lpReplicaSameProfileCounterSj
      lpReplicaSameProfileCounterT lpReplicaSameProfileCounter_sources
      lpReplicaSameProfileCounter_ghost_disconn)

end StatMech.Ising
