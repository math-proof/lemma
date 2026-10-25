import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.ContourCountInjection.Part2
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[crosses_iff_edgeStraddles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourCountInjection.lean)
-/
@[path]
private lemma crosses_iff_edgeStraddles_eq
  {d : ℕ}
  {K : Set (Site d)}
  {e : Sym2 (Site d)} :
-- imply
  crosses K e ↔ edgeStraddles K e := by
-- proof
  apply StatMech.Lattice.crosses_iff_edgeStraddles K e

/--
[mem_crossEdges_iff_mem_boundaryEdgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourCountInjection.lean)
-/
@[path]
private lemma mem_crossEdges_iff_mem_boundaryEdgeSet_eq
  {d : ℕ}
  {K : Set (Site d)}
  {B : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (hB : ∀ e ∈ B, e ∈ (hypercubicLattice d).edgeSet) :
-- imply
  e ∈ crossEdges K B ↔ (e ∈ B ∧ e ∈ boundaryEdgeSet K) := by
-- proof
  apply StatMech.Lattice.mem_crossEdges_iff_mem_boundaryEdgeSet K B hB e

/--
[mk_mem_bondFinsetTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourCountInjection.lean)
-/
@[path]
private lemma mk_mem_bondFinsetTouch_eq
  {d : ℕ}
  {n : ℕ}
  {x y : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj x y)
  (htouch : x ∈ box d n ∨ y ∈ box d n) :
-- imply
  s(x, y) ∈ bondFinsetTouch d n := by
-- proof
  apply StatMech.Lattice.mk_mem_bondFinsetTouch hadj htouch

/--
[boundaryEdgeSet_subset_bondFinsetTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourCountInjection.lean)
-/
@[path]
private lemma boundaryEdgeSet_subset_bondFinsetTouch_eq
  {d : ℕ}
  {K : Set (Site d)}
  {n : ℕ}
  {e : Sym2 (Site d)}
-- given
  (hKbox : K ⊆ box d n)
  (he : e ∈ boundaryEdgeSet K) :
-- imply
  e ∈ bondFinsetTouch d n := by
-- proof
  apply StatMech.Lattice.boundaryEdgeSet_subset_bondFinsetTouch hKbox he

/--
[bondFinsetTouch_subset_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourCountInjection.lean)
-/
@[path]
private lemma bondFinsetTouch_subset_edgeSet_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  ∀ e ∈ bondFinsetTouch d n, e ∈ (hypercubicLattice d).edgeSet := by
-- proof
  apply StatMech.Lattice.bondFinsetTouch_subset_edgeSet n

/--
[coe_crossEdges_eq_boundaryEdgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourCountInjection.lean)
-/
@[path]
private lemma coe_crossEdges_eq_boundaryEdgeSet_eq
  {d : ℕ}
  {K : Set (Site d)}
  {n : ℕ}
-- given
  (hKbox : K ⊆ box d n) :
-- imply
  (↑(crossEdges K (bondFinsetTouch d n)) : Set (Sym2 (Site d))) = boundaryEdgeSet K := by
-- proof
  apply StatMech.Lattice.coe_crossEdges_eq_boundaryEdgeSet hKbox

/--
[boundaryEdgeSet_eq_of_crossEdges_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourCountInjection.lean)
-/
@[path]
private lemma boundaryEdgeSet_eq_of_crossEdges_eq_eq
  {d : ℕ}
  {K₁ K₂ : Set (Site d)}
  {n : ℕ}
-- given
  (h0 : K₁ ⊆ box d n)
  (h1 : K₂ ⊆ box d n)
  (h : crossEdges K₁ (bondFinsetTouch d n) = crossEdges K₂ (bondFinsetTouch d n)) :
-- imply
  boundaryEdgeSet K₁ = boundaryEdgeSet K₂ := by
-- proof
  apply StatMech.Lattice.boundaryEdgeSet_eq_of_crossEdges_eq h0 h1 h

/--
[connBoxCluster_crossEdges_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourCountInjection.lean)
-/
@[path]
private lemma connBoxCluster_crossEdges_injOn_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  Set.InjOn (fun K : Finset (Site d) => crossEdges (↑K : Set (Site d)) (bondFinsetTouch d n)) (connClusterFamily (d := d) n : Set (Finset (Site d))) := by
-- proof
  apply StatMech.Lattice.connBoxCluster_crossEdges_injOn

/--
[crossEdges_subset_bondFinsetTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourCountInjection.lean)
-/
@[path]
private lemma crossEdges_subset_bondFinsetTouch_eq
  {d : ℕ}
  {K : Set (Site d)}
  {n : ℕ} :
-- imply
  crossEdges K (bondFinsetTouch d n) ⊆ bondFinsetTouch d n := by
-- proof
  apply StatMech.Lattice.crossEdges_subset_bondFinsetTouch K n

/--
[connClusterFamily_card_le_powerset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourCountInjection.lean)
-/
@[path]
private lemma connClusterFamily_card_le_powerset_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  (connClusterFamily (d := d) n).card ≤ (bondFinsetTouch d n).powerset.card := by
-- proof
  apply StatMech.Lattice.connClusterFamily_card_le_powerset n

/--
[connFamily_fixedLen_card_le_subsets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourCountInjection.lean)
-/
@[path]
private lemma connFamily_fixedLen_card_le_subsets_eq
  {d : ℕ}
  {n ℓ : ℕ} :
-- imply
  ((connClusterFamily (d := d) n).filter (fun K : Finset (Site d) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)).card ≤ ((bondFinsetTouch d n).powerset.filter (fun E => E.card = ℓ)).card := by
-- proof
  apply StatMech.Lattice.connFamily_fixedLen_card_le_subsets n ℓ

/--
[connFamily_fixedLen_card_eq_realised](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourCountInjection.lean)
-/
@[path]
private lemma connFamily_fixedLen_card_eq_realised_eq
  {d : ℕ}
  {n ℓ : ℕ} :
-- imply
  ((connClusterFamily (d := d) n).filter (fun K : Finset (Site d) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)).card = (realisedContours d n ℓ).card := by
-- proof
  apply StatMech.Lattice.connFamily_fixedLen_card_eq_realised n ℓ

/--
[connFamily_fixedLen_card_le_peierls](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourCountInjection.lean)
-/
@[path]
private lemma connFamily_fixedLen_card_le_peierls_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (h : ContourSubsetCountBound d n ℓ) :
-- imply
  ((connClusterFamily (d := d) n).filter (fun K : Finset (Site d) => contourLen (↑K) (bondFinsetTouch d n) = ℓ)).card ≤ ℓ * (2 * d) ^ ℓ := by
-- proof
  apply StatMech.Lattice.connFamily_fixedLen_card_le_peierls n ℓ h

/--
[singleton_origin_isConnectedCluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourCountInjection.lean)
-/
@[path]
private lemma singleton_origin_isConnectedCluster_eq
  {d : ℕ} :
-- imply
  IsConnectedCluster ({origin d} : Finset (Site d)) := by
-- proof
  apply StatMech.Lattice.singleton_origin_isConnectedCluster


-- created on 2026-10-23
