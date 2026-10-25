import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
open Set Finset StatMech StatMech.Lattice


/--
[nearestNeighbour_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean)
-/
@[path]
private lemma nearestNeighbour_symm_eq
  {d : ℕ} :
-- imply
  Std.Symm (NearestNeighbour d) := by
-- proof
  apply StatMech.Lattice.nearestNeighbour_symm d

/--
[nearestNeighbour_irrefl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean)
-/
@[path]
private lemma nearestNeighbour_irrefl_eq
  {d : ℕ} :
-- imply
  Std.Irrefl (NearestNeighbour d) := by
-- proof
  apply StatMech.Lattice.nearestNeighbour_irrefl d

/--
[hypercubicLattice_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean)
-/
@[path]
private lemma hypercubicLattice_adj_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  (hypercubicLattice d).Adj x y ↔ (∑ i, (x i - y i).natAbs) = 1 := by
-- proof
  apply StatMech.Lattice.hypercubicLattice_adj d x y

/--
[mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean)
-/
@[path]
private lemma mem_box_eq
  {d n : ℕ}
  {x : Site d} :
-- imply
  x ∈ box d n ↔ ∀ i, (x i).natAbs ≤ n := by
-- proof
  apply StatMech.Lattice.mem_box

/--
[box_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean)
-/
@[path]
private lemma box_finite_eq
  {d n : ℕ} :
-- imply
  (box d n).Finite := by
-- proof
  apply StatMech.Lattice.box_finite d n

/--
[mem_vertexBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean)
-/
@[path]
private lemma mem_vertexBoundary_eq
  {d n : ℕ}
  {x : Site d} :
-- imply
  x ∈ vertexBoundary d n ↔ x ∈ box d n ∧ x ∉ box d (n - 1) := by
-- proof
  apply StatMech.Lattice.mem_vertexBoundary

/--
[vertexBoundary_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean)
-/
@[path]
private lemma vertexBoundary_finite_eq
  {d n : ℕ} :
-- imply
  (vertexBoundary d n).Finite := by
-- proof
  apply StatMech.Lattice.vertexBoundary_finite d n

/--
[mem_edgeBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean)
-/
@[path]
private lemma mem_edgeBoundary_eq
  {d : ℕ}
  {S : Set (Site d)}
  {x y : Site d} :
-- imply
  (x, y) ∈ edgeBoundary d S ↔ (hypercubicLattice d).Adj x y ∧ (x ∈ S ↔ y ∉ S) := by
-- proof
  apply StatMech.Lattice.mem_edgeBoundary

/--
[edgeBoundary_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean)
-/
@[path]
private lemma edgeBoundary_symm_eq
  {d : ℕ}
  {S : Set (Site d)}
  {x y : Site d}
-- given
  (h : (x, y) ∈ edgeBoundary d S) :
-- imply
  (y, x) ∈ edgeBoundary d S := by
-- proof
  apply StatMech.Lattice.edgeBoundary_symm h

/--
[box_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean)
-/
@[path]
private lemma box_mono_eq
  {d : ℕ} :
-- imply
  Monotone (box d) := by
-- proof
  apply StatMech.Lattice.box_mono d

/--
[box_subset_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean)
-/
@[path]
private lemma box_subset_succ_eq
  {d n : ℕ} :
-- imply
  box d n ⊆ box d (n + 1) := by
-- proof
  apply StatMech.Lattice.box_subset_succ d n

/--
[iUnion_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/HypercubicLattice.lean)
-/
@[path]
private lemma iUnion_box_eq
  {d : ℕ} :
-- imply
  (⋃ n, box d n) = Set.univ := by
-- proof
  apply StatMech.Lattice.iUnion_box d


-- created on 2026-10-23
