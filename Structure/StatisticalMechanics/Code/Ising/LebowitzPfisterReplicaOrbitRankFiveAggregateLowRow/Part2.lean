/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 800000 in


structure LPReplicaLowRowCollisionParallelData
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q) where
  activeCopy : StatMech.Sharpness.FluxEdgeCopy.Copy
    (lpReplicaCurrentGraph G sites) z.1.1.1
  inactiveCopy₀ : StatMech.Sharpness.FluxEdgeCopy.Copy
    (lpReplicaCurrentGraph G sites) z.1.1.1
  inactiveCopy₁ : StatMech.Sharpness.FluxEdgeCopy.Copy
    (lpReplicaCurrentGraph G sites) z.1.1.1
  active_mem : activeCopy ∈ lpReplicaCurrentCopies G sites z.1.1.1
    (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false
  inactive₀_mem : inactiveCopy₀ ∈ Finset.univ \
    lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false
  inactive₁_mem : inactiveCopy₁ ∈ Finset.univ \
    lpReplicaCurrentCopies G sites z.1.1.1
      (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 true false
  inactive₀_parallel : inactiveCopy₀.1.1 = activeCopy.1.1
  inactive₁_parallel : inactiveCopy₁.1.1 = activeCopy.1.1
  inactive₀_tag :
    (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 inactiveCopy₀ =
      (false, false)
  inactive₁_tag :
    (lpReplicaDecoratedSourceRowGateData G sites i j q z).1 inactiveCopy₁ =
      (false, false)
  inactive_ne : inactiveCopy₀ ≠ inactiveCopy₁
  markedSeam : activeCopy.1.1 = lpReplicaCurrentSeamEdge sites i ∨
    activeCopy.1.1 = lpReplicaCurrentSeamEdge sites j

end
end StatMech.Ising
