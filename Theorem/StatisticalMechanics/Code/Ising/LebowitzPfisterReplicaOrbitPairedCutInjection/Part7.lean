/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCrossToggleMatching.Part8
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutHallExact
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitExactTagProjection
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection.Part6
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 800000 in

theorem lpReplicaOrbitCanonicalPenultimateSlot_ne_lastSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
    lpReplicaOrbitCanonicalPenultimateSlot G sites q hcard ≠
      lpReplicaOrbitCanonicalLastSlot G sites q hcard := by
  intro h
  letI : LinearOrder (LPReplicaOrbitCommonSlot G sites q) :=
    LinearOrder.lift' (lpReplicaOrbitCommonSlotOrderKey G sites q)
      (lpReplicaOrbitCommonSlotOrderKey_injective G sites q)
  let E := (Finset.univ : Finset
    (LPReplicaOrbitCommonSlot G sites q)).orderIsoOfFin Finset.card_univ
  let a : Fin (Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :=
    ⟨Fintype.card (LPReplicaOrbitCommonSlot G sites q) - 2, by omega⟩
  let b : Fin (Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :=
    ⟨Fintype.card (LPReplicaOrbitCommonSlot G sites q) - 1, by omega⟩
  have hsub : E a = E b := by
    apply Subtype.ext
    change (E a).1 = (E b).1
    simpa only [a, b, lpReplicaOrbitCanonicalPenultimateSlot,
      lpReplicaOrbitCanonicalLastSlot] using h
  have hfin : a = b := E.injective hsub
  have hval := congrArg (fun z => z.val) hfin
  dsimp only [a, b] at hval
  omega


end
end StatMech.Ising
