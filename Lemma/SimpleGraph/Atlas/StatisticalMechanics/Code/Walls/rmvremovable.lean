import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rmvremovable.Part3
open Finset Set SimpleGraph Function StatMech StatMech.Walls


/--
[rmv_reroute_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_reroute_reachable_eq
  {G : SimpleGraph V}
  {c w : V}
-- given
  (hwc : w ≠ c)
  (hhub : ∀ z, G.Adj c z → z ≠ w → G.Adj w z) :
-- imply
  ∀ (n : ℕ) {x : V} (hx : x ≠ c) (p : G.Walk x w), p.length = n → (G.induce ({c}ᶜ : Set V)).Reachable ⟨x, hx⟩ ⟨w, hwc⟩ := by
-- proof
  apply StatMech.Walls.rmv_reroute_reachable G c w hwc hhub

/--
[rmv_noncut_of_common_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_noncut_of_common_neighbour_eq
  {K : Set (Site 2)}
  {c w : Site 2}
-- given
  (hconn : CellConnected K)
  (hc : c ∈ K)
  (hw : w ∈ K)
  (hwc : w ≠ c)
  (hhub : ∀ z ∈ K, (hypercubicLattice 2).Adj c z → z ≠ w → (hypercubicLattice 2).Adj w z) :
-- imply
  CellConnected (K \ {c}) := by
-- proof
  apply StatMech.Walls.rmv_noncut_of_common_neighbour hconn hc hw hwc hhub

/--
[rmv_adj_diag_leftCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_adj_diag_leftCell_eq
  {c : Site 2} :
-- imply
  (hypercubicLattice 2).Adj (c + ![-1, -1]) (ear_leftCell c) := by
-- proof
  apply StatMech.Walls.rmv_adj_diag_leftCell c

/--
[rmv_adj_diag_downCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_adj_diag_downCell_eq
  {c : Site 2} :
-- imply
  (hypercubicLattice 2).Adj (c + ![-1, -1]) (ear_downCell c) := by
-- proof
  apply StatMech.Walls.rmv_adj_diag_downCell c

/--
[rmv_diag_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_diag_ne_eq
  {c : Site 2} :
-- imply
  c + ![-1, -1] ≠ c := by
-- proof
  apply StatMech.Walls.rmv_diag_ne c

/--
[rmv_extreme_diag_noncut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_extreme_diag_noncut_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hconn : CellConnected K)
  (hc : ear_IsGlobalExtreme K c)
  (hdiag : c + ![-1, -1] ∈ K) :
-- imply
  CellConnected (K \ {c}) := by
-- proof
  apply StatMech.Walls.rmv_extreme_diag_noncut hconn hc hdiag

/--
[rmv_extreme_diag_removable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_extreme_diag_removable_eq
  {K : Finset (Site 2)}
  {c : Site 2}
-- given
  (hconn : IsConnectedCluster K)
  (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
  (hcorigin : c ≠ origin 2)
  (hdiag : c + ![-1, -1] ∈ (↑K : Set (Site 2))) :
-- imply
  ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧ CellConnected ((↑K : Set (Site 2)) \ {d}) := by
-- proof
  apply StatMech.Walls.rmv_extreme_diag_removable hconn hc hcorigin hdiag

/--
[rmv_extreme_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_extreme_dichotomy_eq
  {K : Finset (Site 2)}
  {c : Site 2}
-- given
  (hcard : 2 ≤ K.card)
  (hconn : IsConnectedCluster K)
  (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
  (hcorigin : c ≠ origin 2) :
-- imply
  (∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧ CellConnected ((↑K : Set (Site 2)) \ {d})) ∨ (ear_leftCell c ∈ (↑K : Set (Site 2)) ∧ ear_downCell c ∈ (↑K : Set (Site 2)) ∧ c + ![-1, -1] ∉ (↑K : Set (Site 2))) := by
-- proof
  apply StatMech.Walls.rmv_extreme_dichotomy hcard hconn hc hcorigin

/--
[rmv_mem_block](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_mem_block_eq
  {v : Site 2} :
-- imply
  v ∈ rmv_block ↔ v = ![0, 0] ∨ v = ![1, 0] ∨ v = ![0, 1] ∨ v = ![1, 1] := by
-- proof
  apply StatMech.Walls.rmv_mem_block v

/--
[rmv_block_globalExtreme](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_block_globalExtreme_eq :
-- imply
  ear_IsGlobalExtreme rmv_block ![1, 1] := by
-- proof
  apply StatMech.Walls.rmv_block_globalExtreme

/--
[rmv_block_diag_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_block_diag_mem_eq :
-- imply
  (![1, 1] : Site 2) + ![-1, -1] ∈ rmv_block := by
-- proof
  apply StatMech.Walls.rmv_block_diag_mem

/--
[rmv_block_cellConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_block_cellConnected_eq :
-- imply
  CellConnected rmv_block := by
-- proof
  apply StatMech.Walls.rmv_block_cellConnected

/--
[rmv_block_removable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_block_removable_eq :
-- imply
  CellConnected (rmv_block \ {![1, 1]}) := by
-- proof
  apply StatMech.Walls.rmv_block_removable

/--
[rmv_tromino_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_tromino_nonvacuous_eq :
-- imply
  ∃ c ∈ pc2_tromino, c ≠ origin 2 ∧ (∃ n ∉ pc2_tromino, (hypercubicLattice 2).Adj c n) ∧ CellConnected ((↑pc2_tromino : Set (Site 2)) \ {c}) := by
-- proof
  apply StatMech.Walls.rmv_tromino_nonvacuous

/--
[rmv_vtromino_reflex_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_vtromino_reflex_residue_eq :
-- imply
  (![0, 0] : Site 2) + ![-1, -1] ∉ ear_vtromino ∧ ¬ CellConnected (ear_vtromino \ {![0, 0]}) := by
-- proof
  apply StatMech.Walls.rmv_vtromino_reflex_residue

/--
[rmv_removable_of_extreme_ne_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_removable_of_extreme_ne_origin_eq
  {K : Finset (Site 2)}
  {c : Site 2}
-- given
  (hres : rmv_ReflexCornerResidue)
  (hcard : 2 ≤ K.card)
  (hconn : IsConnectedCluster K)
  (hc : ear_IsGlobalExtreme (↑K : Set (Site 2)) c)
  (hcorigin : c ≠ origin 2) :
-- imply
  ∃ d ∈ K, d ≠ origin 2 ∧ (∃ n ∉ K, (hypercubicLattice 2).Adj d n) ∧ CellConnected ((↑K : Set (Site 2)) \ {d}) := by
-- proof
  apply StatMech.Walls.rmv_removable_of_extreme_ne_origin hres hcard hconn hc hcorigin

/--
[rmv_nbc_of_reflexResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_nbc_of_reflexResidue_eq
-- given
  (hres : rmv_ReflexCornerResidue)
  (hresAnti : rmv_AntiReflexCornerResidue) :
-- imply
  nbc_BoundaryNonCutExists := by
-- proof
  apply StatMech.Walls.rmv_nbc_of_reflexResidue hres hresAnti

/--
[rmv_atc_of_reflexResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_atc_of_reflexResidue_eq
-- given
  (hres : rmv_ReflexCornerResidue)
  (hresAnti : rmv_AntiReflexCornerResidue) :
-- imply
  atc_HasRemovableConnCell := by
-- proof
  apply StatMech.Walls.rmv_atc_of_reflexResidue hres hresAnti

/--
[rmv_fbc_hasRemovableCell_of_reflexResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rmvremovable.lean)
-/
@[path]
private lemma rmv_fbc_hasRemovableCell_of_reflexResidue_eq
-- given
  (hres : rmv_ReflexCornerResidue)
  (hresAnti : rmv_AntiReflexCornerResidue) :
-- imply
  fbc_HasRemovableCell := by
-- proof
  apply StatMech.Walls.rmv_fbc_hasRemovableCell_of_reflexResidue hres hresAnti


-- created on 2026-10-23
