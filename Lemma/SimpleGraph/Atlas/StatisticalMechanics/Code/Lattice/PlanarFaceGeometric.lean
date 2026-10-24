import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric
open SimpleGraph Set StatMech StatMech.Lattice


/--
[regionGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean)
-/
@[path]
private lemma regionGraph_adj_eq
  {G : SimpleGraph (Site 2)}
  {f g : Site 2} :
-- imply
  (regionGraph G).Adj f g ↔ (hypercubicLattice 2).Adj f g ∧ crossEdge.symm s(f, g) ∉ G.edgeSet := by
-- proof
  apply StatMech.Lattice.regionGraph_adj G f g

/--
[regionGraph_le_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean)
-/
@[path]
private lemma regionGraph_le_dual_eq
  {G : SimpleGraph (Site 2)} :
-- imply
  regionGraph G ≤ hypercubicLattice 2 := by
-- proof
  apply StatMech.Lattice.regionGraph_le_dual G

/--
[imageGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean)
-/
@[path]
private lemma imageGraph_adj_eq
  {P : PlanarZ2Subgraph}
  {a b : Site 2} :
-- imply
  (imageGraph P).Adj a b ↔ ∃ x y : P.V, P.G.Adj x y ∧ P.emb x = a ∧ P.emb y = b := by
-- proof
  apply StatMech.Lattice.imageGraph_adj P a b

/--
[imageGraph_le_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean)
-/
@[path]
private lemma imageGraph_le_lattice_eq
  {P : PlanarZ2Subgraph} :
-- imply
  imageGraph P ≤ hypercubicLattice 2 := by
-- proof
  apply StatMech.Lattice.imageGraph_le_lattice P

/--
[mem_box_compl_of_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean)
-/
@[path]
private lemma mem_box_compl_of_exterior_eq
  {R : ℕ}
  {a : Site 2}
-- given
  (h : a ∈ exterior 2 R) :
-- imply
  a ∉ box 2 R := by
-- proof
  apply StatMech.Lattice.mem_box_compl_of_exterior h

/--
[rot90Inv_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean)
-/
@[path]
private lemma rot90Inv_mem_box_eq
  {R : ℕ}
  {x : Site 2}
-- given
  (hx : x ∈ box 2 R) :
-- imply
  rot90Inv x ∈ box 2 R := by
-- proof
  apply StatMech.Lattice.rot90Inv_mem_box R hx

/--
[rot90Fun_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean)
-/
@[path]
private lemma rot90Fun_mem_box_eq
  {R : ℕ}
  {x : Site 2}
-- given
  (hx : x ∈ box 2 R) :
-- imply
  rot90Fun x ∈ box 2 R := by
-- proof
  apply StatMech.Lattice.rot90Fun_mem_box R hx

/--
[image_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean)
-/
@[path]
private lemma image_subset_box_eq
  {P : PlanarZ2Subgraph} :
-- imply
  ∃ R : ℕ, ∀ v : P.V, P.emb v ∈ box 2 R := by
-- proof
  apply StatMech.Lattice.image_subset_box P

/--
[exterior_dual_edge_not_deleted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean)
-/
@[path]
private lemma exterior_dual_edge_not_deleted_eq
  {P : PlanarZ2Subgraph}
  {R : ℕ}
  {f g : Site 2}
-- given
  (hR : ∀ v : P.V, P.emb v ∈ box 2 R)
  (hf : f ∉ box 2 R) :
-- imply
  crossEdge.symm s(f, g) ∉ (imageGraph P).edgeSet := by
-- proof
  apply StatMech.Lattice.exterior_dual_edge_not_deleted P R hR hf

/--
[regionGraph_adj_of_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean)
-/
@[path]
private lemma regionGraph_adj_of_exterior_eq
  {P : PlanarZ2Subgraph}
  {R : ℕ}
  {f g : Site 2}
-- given
  (hR : ∀ v : P.V, P.emb v ∈ box 2 R)
  (hf : f ∉ box 2 R)
  (hadj : (hypercubicLattice 2).Adj f g) :
-- imply
  (regionGraph (imageGraph P)).Adj f g := by
-- proof
  apply StatMech.Lattice.regionGraph_adj_of_exterior P R hR hf hadj

/--
[regionGraph_reachable_of_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean)
-/
@[path]
private lemma regionGraph_reachable_of_exterior_eq
  {P : PlanarZ2Subgraph}
  {R : ℕ}
  {f g : Site 2}
-- given
  (hR : ∀ v : P.V, P.emb v ∈ box 2 R)
  (hf : f ∈ exterior 2 R)
  (hg : g ∈ exterior 2 R)
  (h : ((hypercubicLattice 2).induce (exterior 2 R)).Reachable ⟨f, hf⟩ ⟨g, hg⟩) :
-- imply
  (regionGraph (imageGraph P)).Reachable f g := by
-- proof
  apply StatMech.Lattice.regionGraph_reachable_of_exterior P R hR hf hg h

/--
[exists_infinite_region](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean)
-/
@[path]
private lemma exists_infinite_region_eq
  {P : PlanarZ2Subgraph} :
-- imply
  ∃ C : (regionGraph (imageGraph P)).ConnectedComponent, C.supp.Infinite := by
-- proof
  apply StatMech.Lattice.exists_infinite_region P

/--
[geometricRegionCount_eq_nullity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean)
-/
@[path]
private lemma geometricRegionCount_eq_nullity_eq
  {P : PlanarZ2Subgraph}
-- given
  (hJ : DiscreteJordanSeparation P) :
-- imply
  geometricRegionCount P = nullity P.G := by
-- proof
  apply StatMech.Lattice.geometricRegionCount_eq_nullity P hJ

/--
[faceCount_eq_geometric_regions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean)
-/
@[path]
private lemma faceCount_eq_geometric_regions_eq
  {P : PlanarZ2Subgraph}
-- given
  (hJ : DiscreteJordanSeparation P) :
-- imply
  faceCount P.G = geometricRegionCount P + 1 := by
-- proof
  apply StatMech.Lattice.faceCount_eq_geometric_regions P hJ

/--
[euler_geometric_regions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean)
-/
@[path]
private lemma euler_geometric_regions_eq
  {P : PlanarZ2Subgraph}
-- given
  (hJ : DiscreteJordanSeparation P) :
-- imply
  (Nat.card P.V : ℤ) - P.G.edgeSet.ncard + (geometricRegionCount P + 1) = 1 + Nat.card P.G.ConnectedComponent := by
-- proof
  apply StatMech.Lattice.euler_geometric_regions P hJ

/--
[euler_geometric_regions_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarFaceGeometric.lean)
-/
@[path]
private lemma euler_geometric_regions_connected_eq
  {P : PlanarZ2Subgraph}
-- given
  (hJ : DiscreteJordanSeparation P)
  (hC : P.G.Connected) :
-- imply
  (Nat.card P.V : ℤ) - P.G.edgeSet.ncard + (geometricRegionCount P + 1) = 2 := by
-- proof
  apply StatMech.Lattice.euler_geometric_regions_connected P hJ hC


-- created on 2026-10-23
