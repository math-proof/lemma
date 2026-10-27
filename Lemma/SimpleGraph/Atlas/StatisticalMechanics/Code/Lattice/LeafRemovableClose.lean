import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.LeafRemovableClose.Part2
open Set SimpleGraph StatMech StatMech.Lattice


/--
[lrc_farLeft_offS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_farLeft_offS_eq
  {S : Set (Site 2)}
  {b : ℤ}
  {z : Site 2}
-- given
  (hb : ∀ q ∈ S, b ≤ q 0)
  (hz : z 0 ≤ b - 1) :
-- imply
  z ∉ S := by
-- proof
  apply StatMech.Lattice.lrc_farLeft_offS hb hz

/--
[lrc_reachesFarLeft_offS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_reachesFarLeft_offS_eq
  {S : Set (Site 2)}
  {b : ℤ}
  {x : Site 2}
-- given
  (hS : arcns_OffSupportConnected S)
  (hb : ∀ q ∈ S, b ≤ q 0)
  (hx : x ∉ S) :
-- imply
  ∃ p : (hypercubicLattice 2).Walk x ![b - 1, x 1], (∀ w ∈ p.support, w ∉ S) := by
-- proof
  apply StatMech.Lattice.lrc_reachesFarLeft_offS hS hb hx

/--
[lrc_cell_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_cell_ne_eq
  {a b c d : ℤ}
-- given
  (h : a ≠ c ∨ b ≠ d) :
-- imply
  (![a, b] : Site 2) ≠ ![c, d] := by
-- proof
  apply StatMech.Lattice.lrc_cell_ne h

/--
[lrc_uPrime_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_uPrime_not_mem_eq :
-- imply
  lrc_uPrime ∉ lrc_ringS := by
-- proof
  apply StatMech.Lattice.lrc_uPrime_not_mem

/--
[lrc_origin_neighbours_in_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_origin_neighbours_in_barrier_eq :
-- imply
  (![1, 0] : Site 2) ∈ insert lrc_uPrime lrc_ringS ∧ (![-1, 0] : Site 2) ∈ insert lrc_uPrime lrc_ringS ∧ (![0, 1] : Site 2) ∈ insert lrc_uPrime lrc_ringS ∧ (![0, -1] : Site 2) ∈ insert lrc_uPrime lrc_ringS := by
-- proof
  apply StatMech.Lattice.lrc_origin_neighbours_in_barrier

/--
[lrc_origin_off_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_origin_off_barrier_eq :
-- imply
  (![0, 0] : Site 2) ∉ insert lrc_uPrime lrc_ringS := by
-- proof
  apply StatMech.Lattice.lrc_origin_off_barrier

/--
[lrc_east_off_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_east_off_barrier_eq :
-- imply
  (![2, 0] : Site 2) ∉ insert lrc_uPrime lrc_ringS := by
-- proof
  apply StatMech.Lattice.lrc_east_off_barrier

/--
[lrc_adj_origin_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_adj_origin_cases_eq
  {z : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj ![0, 0] z) :
-- imply
  z = ![1, 0] ∨ z = ![-1, 0] ∨ z = ![0, 1] ∨ z = ![0, -1] := by
-- proof
  apply StatMech.Lattice.lrc_adj_origin_cases h

/--
[lrc_origin_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_origin_isolated_eq
  {z : Site 2} :
-- imply
  ¬ (ffc_offSupportLattice (insert lrc_uPrime lrc_ringS)).Adj ![0, 0] z := by
-- proof
  apply StatMech.Lattice.lrc_origin_isolated

/--
[lrc_eq_of_walk_from_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_eq_of_walk_from_isolated_eq
  {G : SimpleGraph V}
  {a b : V}
  {w : G.Walk a b}
-- given
  (hiso : ∀ z, ¬ G.Adj a z) :
-- imply
  a = b := by
-- proof
  apply StatMech.Lattice.lrc_eq_of_walk_from_isolated w hiso

/--
[lrc_origin_not_reachable_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_origin_not_reachable_east_eq :
-- imply
  ¬ (ffc_offSupportLattice (insert lrc_uPrime lrc_ringS)).Reachable ![0, 0] ![2, 0] := by
-- proof
  apply StatMech.Lattice.lrc_origin_not_reachable_east

/--
[lrc_insert_not_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_insert_not_connected_eq :
-- imply
  ¬ arcns_OffSupportConnected (insert lrc_uPrime lrc_ringS) := by
-- proof
  apply StatMech.Lattice.lrc_insert_not_connected

/--
[lrc_ringS_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_ringS_subset_box_eq :
-- imply
  lrc_ringS ⊆ box 2 1 := by
-- proof
  apply StatMech.Lattice.lrc_ringS_subset_box

/--
[lrc_box_off_ring_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_box_off_ring_cases_eq
  {z : Site 2}
-- given
  (hbox : z ∈ box 2 1)
  (hoff : z ∉ lrc_ringS) :
-- imply
  z = ![0, 0] ∨ z = ![1, 0] := by
-- proof
  apply StatMech.Lattice.lrc_box_off_ring_cases hbox hoff

/--
[lrc_row0_clear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_row0_clear_eq
  {c t : ℤ}
-- given
  (hc : 0 ≤ c)
  (ht : t ∈ Set.uIcc c (1 + 1 : ℤ)) :
-- imply
  (![t, 0] : Site 2) ∉ lrc_ringS := by
-- proof
  apply StatMech.Lattice.lrc_row0_clear hc ht

/--
[lrc_origin_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_origin_reachesExterior_eq :
-- imply
  ∃ (e : Site 2) (p : (hypercubicLattice 2).Walk ![0, 0] e), (∀ w ∈ p.support, w ∉ lrc_ringS) ∧ e ∈ exterior 2 1 := by
-- proof
  apply StatMech.Lattice.lrc_origin_reachesExterior

/--
[lrc_gap_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_gap_reachesExterior_eq :
-- imply
  ∃ (e : Site 2) (p : (hypercubicLattice 2).Walk ![1, 0] e), (∀ w ∈ p.support, w ∉ lrc_ringS) ∧ e ∈ exterior 2 1 := by
-- proof
  apply StatMech.Lattice.lrc_gap_reachesExterior

/--
[lrc_ring_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_ring_reachesExterior_eq :
-- imply
  arcxc_ReachesExterior lrc_ringS 1 := by
-- proof
  apply StatMech.Lattice.lrc_ring_reachesExterior

/--
[lrc_ring_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_ring_connected_eq :
-- imply
  arcns_OffSupportConnected lrc_ringS := by
-- proof
  apply StatMech.Lattice.lrc_ring_connected

/--
[lrc_leafRemovable_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_leafRemovable_false_eq :
-- imply
  ¬ arcns_LeafRemovable lrc_ringS lrc_uPrime := by
-- proof
  apply StatMech.Lattice.lrc_leafRemovable_false

/--
[lrc_leafRemovable_of_reachesFarLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_leafRemovable_of_reachesFarLeft_eq
  {S : Set (Site 2)}
  {u' : Site 2}
-- given
  (h : arcns_ReachesFarLeft (insert u' S)) :
-- imply
  arcns_LeafRemovable S u' := by
-- proof
  apply StatMech.Lattice.lrc_leafRemovable_of_reachesFarLeft h

/--
[lrc_leafRemovable_of_reachesExterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_leafRemovable_of_reachesExterior_eq
  {S : Set (Site 2)}
  {u' : Site 2}
  {R : ℕ}
-- given
  (h : arcxc_ReachesExterior (insert u' S) R) :
-- imply
  arcns_LeafRemovable S u' := by
-- proof
  apply StatMech.Lattice.lrc_leafRemovable_of_reachesExterior h

/--
[lrc_reduction_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeafRemovableClose.lean)
-/
@[path]
private lemma lrc_reduction_nonvacuous_eq :
-- imply
  arcns_LeafRemovable (∅ : Set (Site 2)) ![0, 0] := by
-- proof
  apply StatMech.Lattice.lrc_reduction_nonvacuous


-- created on 2026-10-23
