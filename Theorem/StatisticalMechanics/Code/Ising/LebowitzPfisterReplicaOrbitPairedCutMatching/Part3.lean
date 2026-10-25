/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSequentialExchange.Part5
import Structure.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutMatching
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagCoupledPairedOutputCard_of_profileAllocation
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (a : LPReplicaOffdiagCoupledPairedProfileAllocation
      G sites i j q) :
    Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <=
      (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card := by
  rw [lpReplicaOffdiagCoupledPairedSource_card_eq_sum_profileFibers,
    lpReplicaOffdiagCoupledPairedOutputs_card_eq_sum_profileFibers]
  let R := lpReplicaOffdiagCoupledPairedRelevantProfiles G sites i j q
  calc
    (∑ m ∈ R,
        (lpReplicaOffdiagDecoratedSourcesAtProfile
          G sites i j q m).card) <=
        ∑ m ∈ R, ∑ n ∈ R, a.flow m n := by
      exact Finset.sum_le_sum a.covers
    _ = ∑ n ∈ R, ∑ m ∈ R, a.flow m n := by
      rw [Finset.sum_comm]
    _ <= ∑ n ∈ R,
        (lpReplicaOffdiagCoupledPairedOutputsAtProfile
          G sites i j q n).card := by
      exact Finset.sum_le_sum a.capacity

end
end StatMech.Ising
