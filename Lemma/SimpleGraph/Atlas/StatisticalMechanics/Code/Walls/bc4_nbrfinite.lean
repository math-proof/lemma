import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc4_nbrfinite.Part2
open Set SimpleGraph Finset StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc4_adj_origin_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_nbrfinite.lean)
-/
@[path]
private lemma bc4_adj_origin_sum_eq
  {d : ℕ}
  {n : Site d}
-- given
  (h : (hypercubicLattice d).Adj 0 n) :
-- imply
  ∑ j, (n j).natAbs = 1 := by
-- proof
  apply StatMech.Walls.bc4_adj_origin_sum n h

/--
[bc4_witness_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_nbrfinite.lean)
-/
@[path]
private lemma bc4_witness_coord_eq
  {d : ℕ}
  {n : Site d}
-- given
  (h : ∑ j, (n j).natAbs = 1) :
-- imply
  ∃ i, (n i = 1 ∨ n i = -1) ∧ ∀ j, j ≠ i → n j = 0 := by
-- proof
  apply StatMech.Walls.bc4_witness_coord n h

/--
[bc4_openNbr_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_nbrfinite.lean)
-/
@[path]
private lemma bc4_openNbr_adj_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : Site d}
-- given
  (hn : (openSubgraph d ω).Adj 0 n) :
-- imply
  (hypercubicLattice d).Adj 0 n := by
-- proof
  apply StatMech.Walls.bc4_openNbr_adj ω hn

/--
[bc4_openNbr_mem_box_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_nbrfinite.lean)
-/
@[path]
private lemma bc4_openNbr_mem_box_one_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : Site d}
-- given
  (hn : (openSubgraph d ω).Adj 0 n) :
-- imply
  n ∈ box d 1 := by
-- proof
  apply StatMech.Walls.bc4_openNbr_mem_box_one ω hn

/--
[bc4_origin_openNeighbours_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_nbrfinite.lean)
-/
@[path]
private lemma bc4_origin_openNeighbours_subset_box_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  {n : Site d | (openSubgraph d ω).Adj 0 n} ⊆ box d 1 := by
-- proof
  apply StatMech.Walls.bc4_origin_openNeighbours_subset_box ω

/--
[bc4_origin_openNeighbours_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_nbrfinite.lean)
-/
@[path]
private lemma bc4_origin_openNeighbours_finite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  {n : Site d | (openSubgraph d ω).Adj 0 n}.Finite := by
-- proof
  apply StatMech.Walls.bc4_origin_openNeighbours_finite ω

/--
[bc4_nbrKey_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_nbrfinite.lean)
-/
@[path]
private lemma bc4_nbrKey_eq_eq
  {d : ℕ}
  [NeZero d]
  {n : Site d}
-- given
  (h : ∑ j, (n j).natAbs = 1) :
-- imply
  bc4_nbrKey n = ((bc4_witness_coord n h).choose, decide (n ((bc4_witness_coord n h).choose) = 1)) := by
-- proof
  apply StatMech.Walls.bc4_nbrKey_eq n h

/--
[bc4_nbrKey_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_nbrfinite.lean)
-/
@[path]
private lemma bc4_nbrKey_witness_eq
  {d : ℕ}
  [NeZero d]
  {n : Site d}
-- given
  (h : ∑ j, (n j).natAbs = 1) :
-- imply
  (n (bc4_nbrKey n).1 = 1 ∨ n (bc4_nbrKey n).1 = -1) ∧ (∀ j, j ≠ (bc4_nbrKey n).1 → n j = 0) ∧ (bc4_nbrKey n).2 = decide (n (bc4_nbrKey n).1 = 1) := by
-- proof
  apply StatMech.Walls.bc4_nbrKey_witness n h

/--
[bc4_nbr_eq_of_key](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_nbrfinite.lean)
-/
@[path]
private lemma bc4_nbr_eq_of_key_eq
  {d : ℕ}
  {n m : Site d}
  {i : Fin d}
-- given
  (hn1 : n i = 1 ∨ n i = -1)
  (hnz : ∀ j, j ≠ i → n j = 0)
  (hm1 : m i = 1 ∨ m i = -1)
  (hmz : ∀ j, j ≠ i → m j = 0)
  (hsign : decide (n i = 1) = decide (m i = 1)) :
-- imply
  n = m := by
-- proof
  apply StatMech.Walls.bc4_nbr_eq_of_key hn1 hnz hm1 hmz hsign

/--
[bc4_nbrKey_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_nbrfinite.lean)
-/
@[path]
private lemma bc4_nbrKey_injOn_eq
  {d : ℕ}
  [NeZero d] :
-- imply
  Set.InjOn bc4_nbrKey {n : Site d | (hypercubicLattice d).Adj 0 n} := by
-- proof
  apply StatMech.Walls.bc4_nbrKey_injOn

/--
[bc4_origin_latticeNeighbours_ncard_le_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_nbrfinite.lean)
-/
@[path]
private lemma bc4_origin_latticeNeighbours_ncard_le_pos_eq
  {d : ℕ}
  [NeZero d] :
-- imply
  {n : Site d | (hypercubicLattice d).Adj 0 n}.ncard ≤ 2 * d := by
-- proof
  apply StatMech.Walls.bc4_origin_latticeNeighbours_ncard_le_pos

/--
[bc4_origin_latticeNeighbours_ncard_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_nbrfinite.lean)
-/
@[path]
private lemma bc4_origin_latticeNeighbours_ncard_le_eq
  {d : ℕ} :
-- imply
  {n : Site d | (hypercubicLattice d).Adj 0 n}.ncard ≤ 2 * d := by
-- proof
  apply StatMech.Walls.bc4_origin_latticeNeighbours_ncard_le

/--
[bc4_origin_openNeighbours_ncard_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc4_nbrfinite.lean)
-/
@[path]
private lemma bc4_origin_openNeighbours_ncard_le_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  {n : Site d | (openSubgraph d ω).Adj 0 n}.ncard ≤ 2 * d := by
-- proof
  apply StatMech.Walls.bc4_origin_openNeighbours_ncard_le ω


-- created on 2026-10-23
