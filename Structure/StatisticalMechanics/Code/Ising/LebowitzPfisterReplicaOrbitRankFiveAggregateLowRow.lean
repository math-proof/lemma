/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.Part6
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

structure LPReplicaLowRowMarkedOutputData
    (G : SimpleGraph V) (sites : I -> V) {i j : I}
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) where
  output : LPReplicaOffdiagDecoratedTarget G sites i j q
  copy : StatMech.Sharpness.FluxEdgeCopy.Copy
    (lpReplicaCurrentGraph G sites) z.1.1.1
  copy_active : copy ∈ lpReplicaCurrentCopies G sites z.1.1.1
    (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false
  balanced : LPReplicaOffdiagBalancedOutput G sites i j q output
  branch :
    (∃ y, output = Sum.inl y ∧
      copy.1.1 = lpReplicaCurrentSeamEdge sites i) ∨
    (∃ y, output = Sum.inr y ∧
      copy.1.1 = lpReplicaCurrentSeamEdge sites j)
  state_eq :
    (lpReplicaOffdiagDecoratedTargetBranchedSlotState
        G sites i j q output).2 =
      lpReplicaOrbitFourColorSlotCrossToggle G sites q
        (lpReplicaOrbitCommonSlotsOfCopies G sites q z.1.1.1
          z.1.1.2 z.2.2 {copy})
        (lpReplicaOffdiagDecoratedSourceSlotState G sites i j q z)


end
end StatMech.Ising
