import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourClose2.Part7
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[symPrimal_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma symPrimal_comm_eq
  {f g : Site 2} :
-- imply
  symPrimal f g = symPrimal g f := by
-- proof
  apply StatMech.Lattice.symPrimal_comm f g

/--
[symPrimal_eq_shared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma symPrimal_eq_shared_eq
  {f g : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj f g) :
-- imply
  symPrimal f g = sharedPrimalEdge f g := by
-- proof
  apply StatMech.Lattice.symPrimal_eq_shared h

/--
[symPrimalSym_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma symPrimalSym_mk_eq
  {f g : Site 2} :
-- imply
  symPrimalSym s(f, g) = symPrimal f g := by
-- proof
  apply StatMech.Lattice.symPrimalSym_mk f g

/--
[flankFaces_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma flankFaces_comm_eq
  {p q : Site 2} :
-- imply
  flankFaces p q = flankFaces q p := by
-- proof
  apply StatMech.Lattice.flankFaces_comm p q

/--
[flankFacesSym_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma flankFacesSym_mk_eq
  {p q : Site 2} :
-- imply
  flankFacesSym s(p, q) = flankFaces p q := by
-- proof
  apply StatMech.Lattice.flankFacesSym_mk p q

/--
[adj_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma adj_cases_eq
  {f g : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj f g) :
-- imply
  (f 0 = g 0 ∧ (f 1 = g 1 + 1 ∨ g 1 = f 1 + 1)) ∨ (f 1 = g 1 ∧ (f 0 = g 0 + 1 ∨ g 0 = f 0 + 1)) := by
-- proof
  apply StatMech.Lattice.adj_cases h

/--
[cons_eq_site](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma cons_eq_site_eq
  {f : Site 2}
  {a b : ℤ}
-- given
  (ha : a = f 0)
  (hb : b = f 1) :
-- imply
  ![a, b] = f := by
-- proof
  apply StatMech.Lattice.cons_eq_site ha hb

/--
[flankFacesSym_symPrimal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma flankFacesSym_symPrimal_eq
  {f g : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj f g) :
-- imply
  flankFacesSym (symPrimal f g) = s(f, g) := by
-- proof
  apply StatMech.Lattice.flankFacesSym_symPrimal h

/--
[symPrimalSym_flankFaces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma symPrimalSym_flankFaces_eq
  {p q : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj p q) :
-- imply
  symPrimalSym (flankFaces p q) = s(p, q) := by
-- proof
  apply StatMech.Lattice.symPrimalSym_flankFaces h

/--
[flankFaces_latAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma flankFaces_latAdj_eq
  {p q : Site 2}
-- given
  (h : (hypercubicLattice 2).Adj p q) :
-- imply
  ∃ f g : Site 2, flankFaces p q = s(f, g) ∧ (hypercubicLattice 2).Adj f g := by
-- proof
  apply StatMech.Lattice.flankFaces_latAdj h

/--
[flankFacesSym_mem_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma flankFacesSym_mem_edgeSet_eq
  {K : Set (Site 2)}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ boundaryEdgeSet K) :
-- imply
  flankFacesSym e ∈ (faceBoundaryGraph K).edgeSet ∧ symPrimalSym (flankFacesSym e) = e := by
-- proof
  apply StatMech.Lattice.flankFacesSym_mem_edgeSet he

/--
[symPrimalSym_mem_boundaryEdgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma symPrimalSym_mem_boundaryEdgeSet_eq
  {K : Set (Site 2)}
  {e : Sym2 (Site 2)}
-- given
  (he : e ∈ (faceBoundaryGraph K).edgeSet) :
-- imply
  symPrimalSym e ∈ boundaryEdgeSet K := by
-- proof
  apply StatMech.Lattice.symPrimalSym_mem_boundaryEdgeSet he

/--
[symPrimalSym_injOn_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma symPrimalSym_injOn_edges_eq
  {K : Set (Site 2)} :
-- imply
  Set.InjOn symPrimalSym ((faceBoundaryGraph K).edgeSet) := by
-- proof
  apply StatMech.Lattice.symPrimalSym_injOn_edges K

/--
[circuit_image_eq_crossEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma circuit_image_eq_crossEdges_eq
  {K : Finset (Site 2)}
  {n : ℕ}
  {u : Site 2}
  {c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk u u}
-- given
  (hKbox : (↑K : Set (Site 2)) ⊆ box 2 n)
  (hcov : ∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet, e ∈ c.edges) :
-- imply
  Finset.image symPrimalSym c.edges.toFinset = crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) := by
-- proof
  apply StatMech.Lattice.circuit_image_eq_crossEdges hKbox c hcov

/--
[circuit_decode_eq_contour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma circuit_decode_eq_contour_eq
  {K : Finset (Site 2)}
  {n : ℕ}
  {u : Site 2}
  {c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk u u}
-- given
  (hKbox : (↑K : Set (Site 2)) ⊆ box 2 n)
  (hcov : ∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet, e ∈ c.edges) :
-- imply
  dualWalkContour ⟨u, c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2)))⟩ = crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) := by
-- proof
  apply StatMech.Lattice.circuit_decode_eq_contour hKbox c hcov

/--
[circuit_length_eq_contourLen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma circuit_length_eq_contourLen_eq
  {K : Finset (Site 2)}
  {n : ℕ}
  {u : Site 2}
  {c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk u u}
-- given
  (hKbox : (↑K : Set (Site 2)) ⊆ box 2 n)
  (htrail : c.IsTrail)
  (hcov : ∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet, e ∈ c.edges) :
-- imply
  (c.mapLe (faceBoundaryGraph_le (↑K : Set (Site 2)))).length = contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) := by
-- proof
  apply StatMech.Lattice.circuit_length_eq_contourLen hKbox c htrail hcov

/--
[axisContourDualCircuit_of_circuitData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma axisContourDualCircuit_of_circuitData_eq
  {n ℓ : ℕ}
-- given
  (h : PeierlsContourCircuitData n ℓ) :
-- imply
  AxisContourDualCircuit 2 n ℓ := by
-- proof
  apply StatMech.Lattice.axisContourDualCircuit_of_circuitData h

/--
[realisedContourWalkEncoding_of_circuitData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma realisedContourWalkEncoding_of_circuitData_eq
  {n ℓ : ℕ}
-- given
  (h : PeierlsContourCircuitData n ℓ) :
-- imply
  RealisedContourWalkEncoding 2 n ℓ := by
-- proof
  apply StatMech.Lattice.realisedContourWalkEncoding_of_circuitData h

/--
[contourSubsetCountBound_of_circuitData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma contourSubsetCountBound_of_circuitData_eq
  {n ℓ : ℕ}
-- given
  (h : PeierlsContourCircuitData n ℓ) :
-- imply
  ContourSubsetCountBound 2 n ℓ := by
-- proof
  apply StatMech.Lattice.contourSubsetCountBound_of_circuitData h

/--
[connFamily_fixedLen_card_le_peierls_of_circuitData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma connFamily_fixedLen_card_le_peierls_of_circuitData_eq
  {n ℓ : ℕ}
-- given
  (h : PeierlsContourCircuitData n ℓ) :
-- imply
  ((connClusterFamily (d := 2) n).filter (fun K : Finset (Site 2) => contourLen (↑K) (bondFinsetTouch 2 n) = ℓ)).card ≤ ℓ * (2 * 2) ^ ℓ := by
-- proof
  apply StatMech.Lattice.connFamily_fixedLen_card_le_peierls_of_circuitData h

/--
[realisedContour_has_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma realisedContour_has_cluster_eq
  {n ℓ : ℕ}
  {F : Finset (Sym2 (Site 2))}
-- given
  (hF : F ∈ realisedContours 2 n ℓ) :
-- imply
  ∃ K : Finset (Site 2), K ∈ connClusterFamily (d := 2) n ∧ (↑K : Set (Site 2)) ⊆ box 2 n ∧ crossEdges (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = F ∧ contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) = ℓ := by
-- proof
  apply StatMech.Lattice.realisedContour_has_cluster hF

/--
[peierlsContourCircuitData_of_geometryResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma peierlsContourCircuitData_of_geometryResidue_eq
  {n ℓ : ℕ}
-- given
  (h : ContourGeometryResidue n ℓ) :
-- imply
  PeierlsContourCircuitData n ℓ := by
-- proof
  apply StatMech.Lattice.peierlsContourCircuitData_of_geometryResidue h

/--
[axisContourDualCircuit_of_geometryResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma axisContourDualCircuit_of_geometryResidue_eq
  {n ℓ : ℕ}
-- given
  (h : ContourGeometryResidue n ℓ) :
-- imply
  AxisContourDualCircuit 2 n ℓ := by
-- proof
  apply StatMech.Lattice.axisContourDualCircuit_of_geometryResidue h

/--
[contourSubsetCountBound_of_geometryResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma contourSubsetCountBound_of_geometryResidue_eq
  {n ℓ : ℕ}
-- given
  (h : ContourGeometryResidue n ℓ) :
-- imply
  ContourSubsetCountBound 2 n ℓ := by
-- proof
  apply StatMech.Lattice.contourSubsetCountBound_of_geometryResidue h

/--
[connFamily_fixedLen_card_le_peierls_of_geometryResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma connFamily_fixedLen_card_le_peierls_of_geometryResidue_eq
  {n ℓ : ℕ}
-- given
  (h : ContourGeometryResidue n ℓ) :
-- imply
  ((connClusterFamily (d := 2) n).filter (fun K : Finset (Site 2) => contourLen (↑K) (bondFinsetTouch 2 n) = ℓ)).card ≤ ℓ * (2 * 2) ^ ℓ := by
-- proof
  apply StatMech.Lattice.connFamily_fixedLen_card_le_peierls_of_geometryResidue h

/--
[peierlsContourCircuitData_of_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma peierlsContourCircuitData_of_empty_eq
  {n ℓ : ℕ}
-- given
  (hempty : realisedContours 2 n ℓ = ∅) :
-- imply
  PeierlsContourCircuitData n ℓ := by
-- proof
  apply StatMech.Lattice.peierlsContourCircuitData_of_empty hempty

/--
[contourGeometryResidue_of_no_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma contourGeometryResidue_of_no_cluster_eq
  {n ℓ : ℕ}
-- given
  (hempty : ∀ K : Finset (Site 2), K ∈ connClusterFamily (d := 2) n → contourLen (↑K : Set (Site 2)) (bondFinsetTouch 2 n) ≠ ℓ) :
-- imply
  ContourGeometryResidue n ℓ := by
-- proof
  apply StatMech.Lattice.contourGeometryResidue_of_no_cluster hempty

/--
[contourSubsetCountBound_of_empty_circuitData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma contourSubsetCountBound_of_empty_circuitData_eq
  {n ℓ : ℕ}
-- given
  (hempty : realisedContours 2 n ℓ = ∅) :
-- imply
  ContourSubsetCountBound 2 n ℓ := by
-- proof
  apply StatMech.Lattice.contourSubsetCountBound_of_empty_circuitData hempty

/--
[peierls_long_range_order_of_geometryResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PeierlsContourClose2.lean)
-/
@[path]
private lemma peierls_long_range_order_of_geometryResidue_eq
-- given
  (h : ∀ (n ℓ : ℕ), ContourGeometryResidue n ℓ) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → StatMech.Ising.plusMeasure 2 n β 0 ≠ StatMech.Ising.minusMeasure 2 n β 0 := by
-- proof
  apply StatMech.Lattice.peierls_long_range_order_of_geometryResidue h


-- created on 2026-10-23
