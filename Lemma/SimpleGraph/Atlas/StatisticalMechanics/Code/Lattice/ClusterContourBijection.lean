import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.ClusterContourBijection
open Set Finset StatMech StatMech.Lattice


/--
[ccb_adj_mem_box_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterContourBijection.lean)
-/
@[path]
private lemma ccb_adj_mem_box_succ_eq
  {d : ℕ}
  {n : ℕ}
  {x y : Site d}
-- given
  (h : (hypercubicLattice d).Adj x y)
  (hx : x ∈ box d n) :
-- imply
  y ∈ box d (n + 1) := by
-- proof
  apply StatMech.Lattice.ccb_adj_mem_box_succ h hx

/--
[ccb_boundary_step_mem_crossEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterContourBijection.lean)
-/
@[path]
private lemma ccb_boundary_step_mem_crossEdges_eq
  {d : ℕ}
  {K : Finset (Site d)}
  {n : ℕ}
  {a b : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj a b)
  (haK : a ∈ K)
  (hbK : b ∉ K)
  (hab : a ∈ box d n) :
-- imply
  s(a, b) ∈ crossEdges (↑K : Set (Site d)) (bondFinsetTouch d n) := by
-- proof
  apply StatMech.Lattice.ccb_boundary_step_mem_crossEdges hadj haK hbK hab

/--
[ccb_walk_stays_in_K](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterContourBijection.lean)
-/
@[path]
private lemma ccb_walk_stays_in_K_eq
  {d : ℕ}
  {K : Finset (Site d)}
  {n : ℕ}
-- given
  (hsub : (↑K : Set (Site d)) ⊆ box d n) :
-- imply
  ∀ {a x : Site d}, ((hypercubicLattice d).deleteEdges ↑(crossEdges (↑K) (bondFinsetTouch d n))).Walk a x → a ∈ K → x ∈ K := by
-- proof
  apply StatMech.Lattice.ccb_walk_stays_in_K hsub

/--
[ccb_regionDel_crossEdges_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterContourBijection.lean)
-/
@[path]
private lemma ccb_regionDel_crossEdges_eq_eq
  {d : ℕ}
  {K : Finset (Site d)}
  {n : ℕ}
-- given
  (hconn : IsConnectedCluster K)
  (hsub : (↑K : Set (Site d)) ⊆ box d n) :
-- imply
  regionDel d ↑(crossEdges (↑K) (bondFinsetTouch d n)) = (↑K : Set (Site d)) := by
-- proof
  apply StatMech.Lattice.ccb_regionDel_crossEdges_eq hconn hsub

/--
[ccb_crossEdges_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterContourBijection.lean)
-/
@[path]
private lemma ccb_crossEdges_injOn_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  Set.InjOn (fun K : Finset (Site d) => crossEdges (↑K) (bondFinsetTouch d n)) {K | IsConnectedCluster K ∧ (↑K : Set (Site d)) ⊆ box d n} := by
-- proof
  apply StatMech.Lattice.ccb_crossEdges_injOn

/--
[ccb_connClusterFamily_props](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterContourBijection.lean)
-/
@[path]
private lemma ccb_connClusterFamily_props_eq
  {d : ℕ}
  {n : ℕ}
  {K : Finset (Site d)}
-- given
  (hK : K ∈ connClusterFamily (d := d) n) :
-- imply
  IsConnectedCluster K ∧ (↑K : Set (Site d)) ⊆ box d n := by
-- proof
  apply StatMech.Lattice.ccb_connClusterFamily_props hK

/--
[ccb_connectedContourCount_of_encoding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterContourBijection.lean)
-/
@[path]
private lemma ccb_connectedContourCount_of_encoding_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : ∀ ℓ, ccb_ContourEncodingExists d n ℓ) :
-- imply
  ConnectedContourCount d n := by
-- proof
  apply StatMech.Lattice.ccb_connectedContourCount_of_encoding h

/--
[ccb_contourEncodingExists_of_decode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterContourBijection.lean)
-/
@[path]
private lemma ccb_contourEncodingExists_of_decode_eq
  {d : ℕ}
  {n ℓ : ℕ}
  {anchors : Finset (Site d)}
  {enc : Finset (Site d) → Σ v : Site d, (hypercubicLattice d).Walk v v}
  {decode : (Σ v : Site d, (hypercubicLattice d).Walk v v) → Finset (Sym2 (Site d))}
-- given
  (hanc : anchors.card ≤ ℓ)
  (hmaps : ∀ K ∈ ccb_contourFiber d n ℓ, (enc K).1 ∈ anchors ∧ (enc K).2.length = ℓ)
  (hdec : ∀ K ∈ ccb_contourFiber d n ℓ, decode (enc K) = crossEdges (↑K) (bondFinsetTouch d n)) :
-- imply
  ccb_ContourEncodingExists d n ℓ := by
-- proof
  apply StatMech.Lattice.ccb_contourEncodingExists_of_decode n ℓ anchors hanc enc hmaps decode hdec

/--
[ccb_peierls_long_range_order_of_encoding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ClusterContourBijection.lean)
-/
@[path]
private lemma ccb_peierls_long_range_order_of_encoding_eq
  {d : ℕ}
-- given
  (hd : 2 ≤ d)
  (hEnc : ∀ (n ℓ : ℕ), ccb_ContourEncodingExists d n ℓ) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → Ising.plusMeasure d n β 0 ≠ Ising.minusMeasure d n β 0 := by
-- proof
  apply StatMech.Lattice.ccb_peierls_long_range_order_of_encoding hd hEnc


-- created on 2026-10-23
