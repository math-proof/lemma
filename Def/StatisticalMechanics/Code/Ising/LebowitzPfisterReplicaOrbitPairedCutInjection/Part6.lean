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
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection.Part6
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def lpReplicaOrbitCanonicalLastSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
    LPReplicaOrbitCommonSlot G sites q := by
  letI : LinearOrder (LPReplicaOrbitCommonSlot G sites q) :=
    LinearOrder.lift' (lpReplicaOrbitCommonSlotOrderKey G sites q)
      (lpReplicaOrbitCommonSlotOrderKey_injective G sites q)
  let E := ((Finset.univ : Finset
    (LPReplicaOrbitCommonSlot G sites q)).orderIsoOfFin rfl)
  exact (E ⟨Fintype.card (LPReplicaOrbitCommonSlot G sites q) - 1, by
    simpa only [Finset.card_univ] using
      (Nat.sub_lt (by omega) (by omega))⟩).1


noncomputable def lpReplicaOrbitCanonicalPenultimateSlot
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : 2 <= Fintype.card (LPReplicaOrbitCommonSlot G sites q)) :
    LPReplicaOrbitCommonSlot G sites q := by
  letI : LinearOrder (LPReplicaOrbitCommonSlot G sites q) :=
    LinearOrder.lift' (lpReplicaOrbitCommonSlotOrderKey G sites q)
      (lpReplicaOrbitCommonSlotOrderKey_injective G sites q)
  let E := ((Finset.univ : Finset
    (LPReplicaOrbitCommonSlot G sites q)).orderIsoOfFin rfl)
  exact (E ⟨Fintype.card (LPReplicaOrbitCommonSlot G sites q) - 2, by
    simpa only [Finset.card_univ] using
      (Nat.sub_lt (by omega) (by omega))⟩).1

end
end StatMech.Ising
