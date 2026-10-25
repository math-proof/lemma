import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.wcscornersum.Part5
open Finset SimpleGraph Function StatMech StatMech.Wcs


/--
[siteToVtx_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma siteToVtx_apply_eq
  {f : Site 2} :
-- imply
  siteToVtx f = (f 0, f 1) := by
-- proof
  apply StatMech.Wcs.siteToVtx_apply f

/--
[siteToVtx_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma siteToVtx_symm_apply_eq
  {p : ℤ × ℤ} :
-- imply
  siteToVtx.symm p = ![p.1, p.2] := by
-- proof
  apply StatMech.Wcs.siteToVtx_symm_apply p

/--
[siteToVtx_symm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma siteToVtx_symm_zero_eq
  {p : ℤ × ℤ} :
-- imply
  (siteToVtx.symm p) 0 = p.1 := by
-- proof
  apply StatMech.Wcs.siteToVtx_symm_zero p

/--
[siteToVtx_symm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma siteToVtx_symm_one_eq
  {p : ℤ × ℤ} :
-- imply
  (siteToVtx.symm p) 1 = p.2 := by
-- proof
  apply StatMech.Wcs.siteToVtx_symm_one p

/--
[mem_toVtxSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma mem_toVtxSet_eq
  {K : Set (Site 2)}
  {p : ℤ × ℤ} :
-- imply
  p ∈ toVtxSet K ↔ siteToVtx.symm p ∈ K := by
-- proof
  apply StatMech.Wcs.mem_toVtxSet K p

/--
[mem_toVtxFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma mem_toVtxFinset_eq
  {K : Set (Site 2)}
  {p : ℤ × ℤ}
-- given
  (hK : K.Finite) :
-- imply
  p ∈ toVtxFinset K hK ↔ siteToVtx.symm p ∈ K := by
-- proof
  apply StatMech.Wcs.mem_toVtxFinset K hK p

/--
[siteToVtx_mem_toVtxFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma siteToVtx_mem_toVtxFinset_eq
  {K : Set (Site 2)}
  {s : Site 2}
-- given
  (hK : K.Finite) :
-- imply
  siteToVtx s ∈ toVtxFinset K hK ↔ s ∈ K := by
-- proof
  apply StatMech.Wcs.siteToVtx_mem_toVtxFinset K hK s

/--
[wcs_turnZ_probe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma wcs_turnZ_probe_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  turnZ K e = (if frontCell e ∈ K then 1 else if sideCell e ∈ K then 0 else -1) := by
-- proof
  apply StatMech.Wcs.wcs_turnZ_probe K e

/--
[wcs_turnZ_eq_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma wcs_turnZ_eq_one_iff_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  turnZ K e = 1 ↔ frontCell e ∈ K := by
-- proof
  apply StatMech.Wcs.wcs_turnZ_eq_one_iff K e

/--
[wcs_turnZ_eq_negone_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma wcs_turnZ_eq_negone_iff_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  turnZ K e = -1 ↔ (frontCell e ∉ K ∧ sideCell e ∉ K) := by
-- proof
  apply StatMech.Wcs.wcs_turnZ_eq_negone_iff K e

/--
[wcs_turnZ_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma wcs_turnZ_eq_zero_iff_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  turnZ K e = 0 ↔ (frontCell e ∉ K ∧ sideCell e ∈ K) := by
-- proof
  apply StatMech.Wcs.wcs_turnZ_eq_zero_iff K e

/--
[wcs_dir_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma wcs_dir_cases_eq
  {e : Dart} :
-- imply
  e.dir = ![1, 0] ∨ e.dir = ![-1, 0] ∨ e.dir = ![0, 1] ∨ e.dir = ![0, -1] := by
-- proof
  apply StatMech.Wcs.wcs_dir_cases e

/--
[siteToVtx_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma siteToVtx_add_eq
  {x y : Site 2} :
-- imply
  siteToVtx (x + y) = (siteToVtx x + siteToVtx y) := by
-- proof
  apply StatMech.Wcs.siteToVtx_add x y

/--
[wcs_surroundCells_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma wcs_surroundCells_pivot_eq
  {e : Dart} :
-- imply
  surroundCells (wcs_pivot e) = ({siteToVtx e.tail, siteToVtx e.head, siteToVtx (sideCell e), siteToVtx (frontCell e)} : Finset (ℤ × ℤ)) := by
-- proof
  apply StatMech.Wcs.wcs_surroundCells_pivot e

/--
[wcs_block_pairwise_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma wcs_block_pairwise_distinct_eq
  {e : Dart} :
-- imply
  (siteToVtx e.tail ≠ siteToVtx e.head) ∧ (siteToVtx e.tail ≠ siteToVtx (sideCell e)) ∧ (siteToVtx e.tail ≠ siteToVtx (frontCell e)) ∧ (siteToVtx e.head ≠ siteToVtx (sideCell e)) ∧ (siteToVtx e.head ≠ siteToVtx (frontCell e)) ∧ (siteToVtx (sideCell e) ≠ siteToVtx (frontCell e)) := by
-- proof
  apply StatMech.Wcs.wcs_block_pairwise_distinct e

/--
[wcs_edgeDeg_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma wcs_edgeDeg_formula_eq
  {K' : Finset (ℤ × ℤ)}
  {x y : ℤ} :
-- imply
  (edgeDeg K' (x, y) : ℤ) = (if (((x, y) ∈ K') ∨ ((x, y - 1) ∈ K')) then 1 else 0) + (if (((x - 1, y) ∈ K') ∨ ((x - 1, y - 1) ∈ K')) then 1 else 0) + (if (((x - 1, y) ∈ K') ∨ ((x, y) ∈ K')) then 1 else 0) + (if (((x - 1, y - 1) ∈ K') ∨ ((x, y - 1) ∈ K')) then 1 else 0) := by
-- proof
  apply StatMech.Wcs.wcs_edgeDeg_formula K' x y

/--
[wcs_edgeDeg_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma wcs_edgeDeg_pivot_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite) :
-- imply
  (edgeDeg (toVtxFinset K hK) (wcs_pivot e) : ℤ) = (if (siteToVtx e.tail ∈ toVtxFinset K hK ∨ siteToVtx e.head ∈ toVtxFinset K hK) then 1 else 0) + (if (siteToVtx e.tail ∈ toVtxFinset K hK ∨ siteToVtx (sideCell e) ∈ toVtxFinset K hK) then 1 else 0) + (if (siteToVtx e.head ∈ toVtxFinset K hK ∨ siteToVtx (frontCell e) ∈ toVtxFinset K hK) then 1 else 0) + (if (siteToVtx (sideCell e) ∈ toVtxFinset K hK ∨ siteToVtx (frontCell e) ∈ toVtxFinset K hK) then 1 else 0) := by
-- proof
  apply StatMech.Wcs.wcs_edgeDeg_pivot K hK e

/--
[wcs_cellDeg_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma wcs_cellDeg_pivot_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (hb : IsBoundaryDart K e) :
-- imply
  cellDeg (toVtxFinset K hK) (wcs_pivot e) = (if siteToVtx (sideCell e) ∈ toVtxFinset K hK then 1 else 0) + (if siteToVtx (frontCell e) ∈ toVtxFinset K hK then 1 else 0) + 1 := by
-- proof
  apply StatMech.Wcs.wcs_cellDeg_pivot K hK e hb

/--
[wcs_pivot_mem_regVerts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma wcs_pivot_mem_regVerts_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (hb : IsBoundaryDart K e) :
-- imply
  wcs_pivot e ∈ regVerts (toVtxFinset K hK) := by
-- proof
  apply StatMech.Wcs.wcs_pivot_mem_regVerts K hK e hb

/--
[wcs_defect_pivot_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma wcs_defect_pivot_eq_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (hb : IsBoundaryDart K e) :
-- imply
  defect (toVtxFinset K hK) (wcs_pivot e) = (if frontCell e ∈ K then if sideCell e ∈ K then -1 else -2 else if sideCell e ∈ K then 0 else 1) := by
-- proof
  apply StatMech.Wcs.wcs_defect_pivot_eq K hK e hb

/--
[wcs_turnZ_eq_neg_defect_of_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean)
-/
@[path]
private lemma wcs_turnZ_eq_neg_defect_of_pivot_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (hb : IsBoundaryDart K e)
  (hnp : ¬(frontCell e ∈ K ∧ sideCell e ∉ K)) :
-- imply
  turnZ K e = - defect (toVtxFinset K hK) (wcs_pivot e) := by
-- proof
  apply StatMech.Wcs.wcs_turnZ_eq_neg_defect_of_pivot K hK e hb hnp


-- created on 2026-10-23
