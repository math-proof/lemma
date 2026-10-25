/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSameProfileCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSecondTransfer.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaSameProfileCounterexample
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.RandomCurrent


def LPReplicaSameProfileTwoBranchSelectorPrinciple : Prop :=
  ∀ (ends : Fin 5 -> Sym2 (Fin 8))
    (Si Sj T : Finset (Fin 8)),
    StatMech.Sharpness.RandomCurrent.sources ends Finset.univ =
        Si ∆ Sj ∆ T ->
    ¬ connK ends Finset.univ 0 1 ->
    ((∃ P : Finset (Fin 5), P ⊆ Finset.univ ∧
        StatMech.Sharpness.RandomCurrent.sources ends P = Sj ∆ T) ∨
      (∃ P : Finset (Fin 5), P ⊆ Finset.univ ∧
        StatMech.Sharpness.RandomCurrent.sources ends P = Si ∆ T))


end StatMech.Ising
