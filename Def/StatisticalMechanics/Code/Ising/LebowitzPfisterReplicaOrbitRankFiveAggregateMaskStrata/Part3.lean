/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.Part6
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateMaskStrata.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def
    lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFiveEmbedding_of_lowOutputInjective
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (u : LPReplicaOrbitFourColorSlotState G sites q)
    (hinjective : Function.Injective
      (lpReplicaLowRowCrossTraceOutput
        G sites hsite hij q hcard u)) :
    ↑(lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive
        G sites i j q u) ↪
      ↑(lpReplicaOffdiagBalancedOutputCrossTraceFiber
        G sites i j q u) := by
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_coe] using
    lpReplicaOffdiagLowOrResolvableHighCrossTraceFiberRankFive_card_le_target_of_lowOutputInjective
      G sites hsite hij q hcard u hinjective

end
end StatMech.Ising
