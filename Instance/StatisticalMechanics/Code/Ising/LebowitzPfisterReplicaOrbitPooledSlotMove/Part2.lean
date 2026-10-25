/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledSlotMove.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport.Part3
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledSlotMove
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

instance instDecidableEqLPReplicaPooledSelectedSlotState
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    DecidableEq (LPReplicaPooledSelectedSlotState G sites q) :=
  Classical.decEq _


noncomputable instance instFintypeLPReplicaPooledSelectedSlotState
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype (LPReplicaPooledSelectedSlotState G sites q) := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let Profile := {m : H.edgeFinset -> Nat //
    lpReplicaSymmetrizedProfile G sites m = q}
  let Selected := {p : H.edgeFinset -> Nat // p <= q}
  let SlotCoord := (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)) ->
    Finset (Fin (q e.1))
  let Target := Profile × Selected ×
    (SlotCoord × SlotCoord × SlotCoord)
  letI : Fintype Profile := lpReplicaProfileOrbitFintype G sites q
  letI : Fintype Selected :=
    StatMech.Sharpness.instFintypeLe H q
  letI : Fintype SlotCoord := by
    dsimp only [SlotCoord]
    infer_instance
  let encode : LPReplicaPooledSelectedSlotState G sites q -> Target := fun z =>
    (⟨z.profile, z.orbit⟩,
      ⟨z.selected, fun e => z.selected_le e |>.trans
        (lpReplicaProfile_le_of_symmetrizedProfile_eq G sites z.orbit e)⟩,
      (z.slots.allocation, z.slots.selectedRep, z.slots.selectedReflect))
  exact Fintype.ofInjective encode (by
    intro x y hxy
    apply LPReplicaPooledSelectedSlotState.ext
    · exact congrArg (fun z => z.1.1) hxy
    · exact congrArg (fun z => z.2.1.1) hxy
    · apply LPReplicaProfileOrbitSlotState.ext
      · exact congrArg (fun z => z.2.2.1) hxy
      · exact congrArg (fun z => z.2.2.2.1) hxy
      · exact congrArg (fun z => z.2.2.2.2) hxy)


end
end StatMech.Ising
