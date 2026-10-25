import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.ContourEncodingClose.Part3
open Set Finset SimpleGraph StatMech.Ising StatMech StatMech.Lattice


/--
[indicatorConfig_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourEncodingClose.lean)
-/
@[path]
private lemma indicatorConfig_mk_eq
  {d : ℕ}
  {K : Finset (Site d)}
  {x y : Site d} :
-- imply
  indicatorConfig K s(x, y) = decide (x ∈ K ∧ y ∈ K) := by
-- proof
  apply StatMech.Lattice.indicatorConfig_mk K x y

/--
[openSubgraph_indicatorConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourEncodingClose.lean)
-/
@[path]
private lemma openSubgraph_indicatorConfig_eq
  {d : ℕ}
  {K : Finset (Site d)} :
-- imply
  openSubgraph d (indicatorConfig K) = latticeOn (↑K : Set (Site d)) := by
-- proof
  apply StatMech.Lattice.openSubgraph_indicatorConfig K

/--
[cluster_indicatorConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourEncodingClose.lean)
-/
@[path]
private lemma cluster_indicatorConfig_eq
  {d : ℕ}
  {K : Finset (Site d)}
-- given
  (hconn : IsConnectedCluster K) :
-- imply
  cluster d (indicatorConfig K) (origin d) = (↑K : Set (Site d)) := by
-- proof
  apply StatMech.Lattice.cluster_indicatorConfig K hconn

/--
[cluster_indicatorConfig_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourEncodingClose.lean)
-/
@[path]
private lemma cluster_indicatorConfig_finite_eq
  {d : ℕ}
  {K : Finset (Site d)}
-- given
  (hconn : IsConnectedCluster K) :
-- imply
  (cluster d (indicatorConfig K) (origin d)).Finite := by
-- proof
  apply StatMech.Lattice.cluster_indicatorConfig_finite K hconn

/--
[ccb_anchorRow_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourEncodingClose.lean)
-/
@[path]
private lemma ccb_anchorRow_card_eq
  {d : ℕ}
  {ℓ : ℕ} :
-- imply
  (ccb_anchorRow ℓ).card ≤ ℓ := by
-- proof
  apply StatMech.Lattice.ccb_anchorRow_card ℓ

/--
[mem_ccb_anchorRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourEncodingClose.lean)
-/
@[path]
private lemma mem_ccb_anchorRow_eq
  {d : ℕ}
  {ℓ : ℕ}
  {v : Site 2} :
-- imply
  v ∈ ccb_anchorRow ℓ ↔ ∃ j : ℕ, j < ℓ ∧ v = ![ (j : ℤ), 0] := by
-- proof
  apply StatMech.Lattice.mem_ccb_anchorRow

/--
[ccb_contourEncodingExists_of_anchoredBoundaryWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourEncodingClose.lean)
-/
@[path]
private lemma ccb_contourEncodingExists_of_anchoredBoundaryWalk_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (h : ccb_AnchoredBoundaryWalkExists n ℓ) :
-- imply
  ccb_ContourEncodingExists 2 n ℓ := by
-- proof
  apply StatMech.Lattice.ccb_contourEncodingExists_of_anchoredBoundaryWalk n ℓ h

/--
[ccb_anchoredBoundaryWalkExists_of_emptyFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourEncodingClose.lean)
-/
@[path]
private lemma ccb_anchoredBoundaryWalkExists_of_emptyFiber_eq
  {d : ℕ}
  {n ℓ : ℕ}
-- given
  (hempty : ccb_contourFiber 2 n ℓ = ∅) :
-- imply
  ccb_AnchoredBoundaryWalkExists n ℓ := by
-- proof
  apply StatMech.Lattice.ccb_anchoredBoundaryWalkExists_of_emptyFiber n ℓ hempty

/--
[ccb_peierls_of_anchoredBoundaryWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourEncodingClose.lean)
-/
@[path]
private lemma ccb_peierls_of_anchoredBoundaryWalk_eq
  {d : ℕ}
-- given
  (h : ∀ (n ℓ : ℕ), ccb_AnchoredBoundaryWalkExists n ℓ) :
-- imply
  ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → Ising.plusMeasure 2 n β 0 ≠ Ising.minusMeasure 2 n β 0 := by
-- proof
  apply StatMech.Lattice.ccb_peierls_of_anchoredBoundaryWalk h


-- created on 2026-10-23
