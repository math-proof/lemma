import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutHallExact
open Finset StatMech StatMech.Ising


/--
[lpReplicaOffdiagCoupledPairedNeighbors_eq_outputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutHallExact.lean)
-/
@[path]
private lemma lpReplicaOffdiagCoupledPairedNeighbors_eq_outputs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaOffdiagCoupledPairedNeighbors G sites i j q z = lpReplicaOffdiagCoupledPairedOutputs G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCoupledPairedNeighbors_eq_outputs G sites i j q z

/--
[lpReplicaOffdiagCoupledPairedNeighbors_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutHallExact.lean)
-/
@[path]
private lemma lpReplicaOffdiagCoupledPairedNeighbors_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {z : LPReplicaOffdiagDecoratedSource G sites i j q}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  (lpReplicaOffdiagCoupledPairedNeighbors G sites i j q z).card = (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCoupledPairedNeighbors_card G sites i j q z

/--
[lpReplicaOffdiagCoupledPaired_biUnion_eq_outputs_of_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutHallExact.lean)
-/
@[path]
private lemma lpReplicaOffdiagCoupledPaired_biUnion_eq_outputs_of_nonempty_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
  {S : Finset (LPReplicaOffdiagDecoratedSource G sites i j q)}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hS : S.Nonempty) :
-- imply
  S.biUnion (lpReplicaOffdiagCoupledPairedNeighbors G sites i j q) = lpReplicaOffdiagCoupledPairedOutputs G sites i j q := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCoupledPaired_biUnion_eq_outputs_of_nonempty G sites i j q S hS

/--
[lpReplicaOffdiagCoupledPairedHall_iff_outputCard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPairedCutHallExact.lean)
-/
@[path]
private lemma lpReplicaOffdiagCoupledPairedHall_iff_outputCard_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j : I}
-- given
  (sites : I -> V)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  LPReplicaOffdiagCoupledPairedHall G sites i j q ↔ Fintype.card (LPReplicaOffdiagDecoratedSource G sites i j q) <= (lpReplicaOffdiagCoupledPairedOutputs G sites i j q).card := by
-- proof
  apply StatMech.Ising.lpReplicaOffdiagCoupledPairedHall_iff_outputCard G sites i j q


-- created on 2026-10-23
