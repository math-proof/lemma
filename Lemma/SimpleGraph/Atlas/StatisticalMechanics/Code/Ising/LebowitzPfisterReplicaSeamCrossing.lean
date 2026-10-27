import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaSeamCrossing
open Finset SimpleGraph StatMech StatMech.Ising


/--
[lpReplicaCurrentLeft_mem_leftSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSeamCrossing.lean)
-/
@[path]
private lemma lpReplicaCurrentLeft_mem_leftSide_eq
  [Fintype V]
  [DecidableEq V]
  {x : V} :
-- imply
  (.inl (.inl x) : LPReplicaCurrentVertex V) ∈ lpReplicaCurrentLeftSide := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentLeft_mem_leftSide x

/--
[lpReplicaCurrentRight_not_mem_leftSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSeamCrossing.lean)
-/
@[path]
private lemma lpReplicaCurrentRight_not_mem_leftSide_eq
  [Fintype V]
  [DecidableEq V]
  {x : V} :
-- imply
  (.inl (.inr x) : LPReplicaCurrentVertex V) ∉ lpReplicaCurrentLeftSide := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentRight_not_mem_leftSide x

/--
[lpReplicaCurrentGhost0_mem_leftSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSeamCrossing.lean)
-/
@[path]
private lemma lpReplicaCurrentGhost0_mem_leftSide_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ lpReplicaCurrentLeftSide := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentGhost0_mem_leftSide

/--
[lpReplicaCurrentGhost1_not_mem_leftSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSeamCrossing.lean)
-/
@[path]
private lemma lpReplicaCurrentGhost1_not_mem_leftSide_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉ lpReplicaCurrentLeftSide := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentGhost1_not_mem_leftSide

/--
[lpReplicaCurrent_mem_leftSide_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSeamCrossing.lean)
-/
@[path]
private lemma lpReplicaCurrent_mem_leftSide_iff_eq
  [Fintype V]
  [DecidableEq V]
  {z : LPReplicaCurrentVertex V} :
-- imply
  z ∈ lpReplicaCurrentLeftSide ↔ (∃ x : V, z = .inl (.inl x)) ∨ z = lpReplicaCurrentGhost0 := by
-- proof
  apply StatMech.Ising.lpReplicaCurrent_mem_leftSide_iff z

/--
[lpReplicaCurrent_not_mem_leftSide_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSeamCrossing.lean)
-/
@[path]
private lemma lpReplicaCurrent_not_mem_leftSide_iff_eq
  [Fintype V]
  [DecidableEq V]
  {z : LPReplicaCurrentVertex V} :
-- imply
  z ∉ lpReplicaCurrentLeftSide ↔ (∃ x : V, z = .inl (.inr x)) ∨ z = lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaCurrent_not_mem_leftSide_iff z

/--
[lpReplicaCurrent_crossingEdge_eq_seam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSeamCrossing.lean)
-/
@[path]
private lemma lpReplicaCurrent_crossingEdge_eq_seam_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {x y : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (hx : x ∈ lpReplicaCurrentLeftSide)
  (hy : y ∉ lpReplicaCurrentLeftSide)
  (hxy : (lpReplicaCurrentGraph G sites).Adj x y) :
-- imply
  ∃ i : I, s(x, y) = lpReplicaCurrentSeamEdge sites i := by
-- proof
  apply StatMech.Ising.lpReplicaCurrent_crossingEdge_eq_seam G sites hx hy hxy

/--
[lpReplicaCurrentWalk_firstSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSeamCrossing.lean)
-/
@[path]
private lemma lpReplicaCurrentWalk_firstSeam_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {x y : LPReplicaCurrentVertex V}
  {w : (lpReplicaCurrentGraph G sites).Walk x y}
-- given
  (sites : I -> V)
  (hx : x ∈ lpReplicaCurrentLeftSide)
  (hy : y ∉ lpReplicaCurrentLeftSide) :
-- imply
  ∃ k i, 1 ≤ k ∧ k ≤ w.length ∧ w.getVert k ∉ lpReplicaCurrentLeftSide ∧ w.getVert (k - 1) ∈ lpReplicaCurrentLeftSide ∧ s(w.getVert (k - 1), w.getVert k) = lpReplicaCurrentSeamEdge sites i ∧ (∀ j < k, w.getVert j ∈ lpReplicaCurrentLeftSide) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentWalk_firstSeam G sites w hx hy

/--
[lpReplicaCurrentGhostWalk_firstSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaSeamCrossing.lean)
-/
@[path]
private lemma lpReplicaCurrentGhostWalk_firstSeam_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {w : (lpReplicaCurrentGraph G sites).Walk lpReplicaCurrentGhost0 lpReplicaCurrentGhost1}
-- given
  (sites : I -> V) :
-- imply
  ∃ k i, 1 ≤ k ∧ k ≤ w.length ∧ w.getVert k ∉ lpReplicaCurrentLeftSide ∧ w.getVert (k - 1) ∈ lpReplicaCurrentLeftSide ∧ s(w.getVert (k - 1), w.getVert k) = lpReplicaCurrentSeamEdge sites i ∧ (∀ j < k, w.getVert j ∈ lpReplicaCurrentLeftSide) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentGhostWalk_firstSeam G sites w


-- created on 2026-10-23
