/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection.Part12
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.Part2


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness.FluxEdgeCopy

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

structure LPReplicaStrictRouteStateFamily
    (G : SimpleGraph V) (sites : I -> V) (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Source Target : Type*) where
  source : Source ↪ LPReplicaOffdiagDecoratedSource G sites i j q
  spatialSlot : Source -> LPReplicaOrbitCommonSlot G sites q
  rowSlot : Source -> LPReplicaOrbitCommonSlot G sites q
  target : Source -> Target
  targetState : Target -> LPReplicaOrbitFourColorSlotState G sites q
  slots_ne : ∀ x, spatialSlot x ≠ rowSlot x
  output_state : ∀ x,
    targetState (target x) =
      lpReplicaOrbitFourColorSlotReflectRowToggle G sites q
        {spatialSlot x} {rowSlot x}
        (lpReplicaOffdiagDecoratedSourceSlotState
          G sites i j q (source x))


end
end StatMech.Ising
