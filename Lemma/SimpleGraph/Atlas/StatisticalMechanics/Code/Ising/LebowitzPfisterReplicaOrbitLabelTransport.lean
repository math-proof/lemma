import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitLabelTransport.Part3
open Finset StatMech StatMech.Ising


/--
[LPReplicaProfileOrbitSlotState.ext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLabelTransport.lean)
-/
@[path]
private lemma ext_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {sites : I -> V}
  {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
  {s t : LPReplicaProfileOrbitSlotState G sites q}
-- given
  (ha : s.allocation = t.allocation)
  (hr : s.selectedRep = t.selectedRep)
  (ht : s.selectedReflect = t.selectedReflect) :
-- imply
  s = t := by
-- proof
  apply StatMech.Ising.LPReplicaProfileOrbitSlotState.ext ha hr ht

/--
[lpReplicaProfileOrbitSlotMove_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLabelTransport.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitSlotMove_involutive_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  Function.Involutive (lpReplicaProfileOrbitSlotMove G sites q) := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitSlotMove_involutive G sites q

/--
[lpReplicaProfileOrbitSlotMove_allocation_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLabelTransport.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitSlotMove_allocation_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {s : LPReplicaProfileOrbitSlotState G sites q}
  {e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  ((lpReplicaProfileOrbitSlotMove G sites q s).allocation e).card = (s.allocation e).card - (s.selectedRep e).card + (s.selectedReflect e).card := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitSlotMove_allocation_card G sites q s e

/--
[lpReplicaProfileOrbitSlotRealizes_move_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitLabelTransport.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitSlotRealizes_move_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {s : LPReplicaProfileOrbitSlotState G sites q}
-- given
  (sites : I -> V)
  (q m p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hp : p <= m) :
-- imply
  LPReplicaProfileOrbitSlotRealizes G sites q m p s ↔ LPReplicaProfileOrbitSlotRealizes G sites q (lpReplicaPartialReflectProfile G sites m p) (fun e => p (lpReplicaCurrentEdgeReflect G sites e)) (lpReplicaProfileOrbitSlotMove G sites q s) := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitSlotRealizes_move_iff G sites q m p hp s


-- created on 2026-10-23
