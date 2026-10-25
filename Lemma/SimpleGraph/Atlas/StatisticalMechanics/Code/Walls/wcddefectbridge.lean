import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.wcddefectbridge.Part5
open Finset SimpleGraph Function StatMech StatMech.Wcd


/--
[wcd_siteToVtx_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_siteToVtx_apply_eq
  {f : Site 2} :
-- imply
  wcd_siteToVtx f = (f 0, f 1) := by
-- proof
  apply StatMech.Wcd.wcd_siteToVtx_apply f

/--
[wcd_mem_toVtxFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_mem_toVtxFinset_eq
  {K : Set (Site 2)}
  {p : ℤ × ℤ}
-- given
  (hK : K.Finite) :
-- imply
  p ∈ wcd_toVtxFinset K hK ↔ wcd_siteToVtx.symm p ∈ K := by
-- proof
  apply StatMech.Wcd.wcd_mem_toVtxFinset K hK p

/--
[wcd_siteToVtx_mem_toVtxFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_siteToVtx_mem_toVtxFinset_eq
  {K : Set (Site 2)}
  {s : Site 2}
-- given
  (hK : K.Finite) :
-- imply
  wcd_siteToVtx s ∈ wcd_toVtxFinset K hK ↔ s ∈ K := by
-- proof
  apply StatMech.Wcd.wcd_siteToVtx_mem_toVtxFinset K hK s

/--
[wcd_turnZ_probe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_turnZ_probe_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  turnZ K e = (if wcd_frontCell e ∈ K then 1 else if wcd_sideCell e ∈ K then 0 else -1) := by
-- proof
  apply StatMech.Wcd.wcd_turnZ_probe K e

/--
[wcd_dir_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_dir_cases_eq
  {e : Dart} :
-- imply
  e.dir = ![1, 0] ∨ e.dir = ![-1, 0] ∨ e.dir = ![0, 1] ∨ e.dir = ![0, -1] := by
-- proof
  apply StatMech.Wcd.wcd_dir_cases e

/--
[wcd_surroundCells_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_surroundCells_pivot_eq
  {e : Dart} :
-- imply
  surroundCells (wcd_pivot e) = ({wcd_siteToVtx e.tail, wcd_siteToVtx e.head, wcd_siteToVtx (wcd_sideCell e), wcd_siteToVtx (wcd_frontCell e)} : Finset (ℤ × ℤ)) := by
-- proof
  apply StatMech.Wcd.wcd_surroundCells_pivot e

/--
[wcd_block_pairwise_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_block_pairwise_distinct_eq
  {e : Dart} :
-- imply
  (wcd_siteToVtx e.tail ≠ wcd_siteToVtx e.head) ∧ (wcd_siteToVtx e.tail ≠ wcd_siteToVtx (wcd_sideCell e)) ∧ (wcd_siteToVtx e.tail ≠ wcd_siteToVtx (wcd_frontCell e)) ∧ (wcd_siteToVtx e.head ≠ wcd_siteToVtx (wcd_sideCell e)) ∧ (wcd_siteToVtx e.head ≠ wcd_siteToVtx (wcd_frontCell e)) ∧ (wcd_siteToVtx (wcd_sideCell e) ≠ wcd_siteToVtx (wcd_frontCell e)) := by
-- proof
  apply StatMech.Wcd.wcd_block_pairwise_distinct e

/--
[wcd_edgeDeg_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_edgeDeg_formula_eq
  {K' : Finset (ℤ × ℤ)}
  {x y : ℤ} :
-- imply
  (edgeDeg K' (x, y) : ℤ) = (if (((x, y) ∈ K') ∨ ((x, y - 1) ∈ K')) then 1 else 0) + (if (((x - 1, y) ∈ K') ∨ ((x - 1, y - 1) ∈ K')) then 1 else 0) + (if (((x - 1, y) ∈ K') ∨ ((x, y) ∈ K')) then 1 else 0) + (if (((x - 1, y - 1) ∈ K') ∨ ((x, y - 1) ∈ K')) then 1 else 0) := by
-- proof
  apply StatMech.Wcd.wcd_edgeDeg_formula K' x y

/--
[wcd_edgeDeg_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_edgeDeg_pivot_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite) :
-- imply
  (edgeDeg (wcd_toVtxFinset K hK) (wcd_pivot e) : ℤ) = (if (wcd_siteToVtx e.tail ∈ wcd_toVtxFinset K hK ∨ wcd_siteToVtx e.head ∈ wcd_toVtxFinset K hK) then 1 else 0) + (if (wcd_siteToVtx e.tail ∈ wcd_toVtxFinset K hK ∨ wcd_siteToVtx (wcd_sideCell e) ∈ wcd_toVtxFinset K hK) then 1 else 0) + (if (wcd_siteToVtx e.head ∈ wcd_toVtxFinset K hK ∨ wcd_siteToVtx (wcd_frontCell e) ∈ wcd_toVtxFinset K hK) then 1 else 0) + (if (wcd_siteToVtx (wcd_sideCell e) ∈ wcd_toVtxFinset K hK ∨ wcd_siteToVtx (wcd_frontCell e) ∈ wcd_toVtxFinset K hK) then 1 else 0) := by
-- proof
  apply StatMech.Wcd.wcd_edgeDeg_pivot K hK e

/--
[wcd_cellDeg_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_cellDeg_pivot_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (hb : IsBoundaryDart K e) :
-- imply
  cellDeg (wcd_toVtxFinset K hK) (wcd_pivot e) = (if wcd_siteToVtx (wcd_sideCell e) ∈ wcd_toVtxFinset K hK then 1 else 0) + (if wcd_siteToVtx (wcd_frontCell e) ∈ wcd_toVtxFinset K hK then 1 else 0) + 1 := by
-- proof
  apply StatMech.Wcd.wcd_cellDeg_pivot K hK e hb

/--
[wcd_pivot_mem_regVerts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_pivot_mem_regVerts_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (hb : IsBoundaryDart K e) :
-- imply
  wcd_pivot e ∈ regVerts (wcd_toVtxFinset K hK) := by
-- proof
  apply StatMech.Wcd.wcd_pivot_mem_regVerts K hK e hb

/--
[wcd_defect_pivot_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_defect_pivot_eq_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (hb : IsBoundaryDart K e) :
-- imply
  defect (wcd_toVtxFinset K hK) (wcd_pivot e) = (if wcd_frontCell e ∈ K then (if wcd_sideCell e ∈ K then -1 else -2) else (if wcd_sideCell e ∈ K then 0 else 1)) := by
-- proof
  apply StatMech.Wcd.wcd_defect_pivot_eq K hK e hb

/--
[wcd_turnZ_eq_neg_defect_of_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_turnZ_eq_neg_defect_of_pivot_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (hb : IsBoundaryDart K e)
  (hnp : ¬(wcd_frontCell e ∈ K ∧ wcd_sideCell e ∉ K)) :
-- imply
  turnZ K e = - defect (wcd_toVtxFinset K hK) (wcd_pivot e) := by
-- proof
  apply StatMech.Wcd.wcd_turnZ_eq_neg_defect_of_pivot K hK e hb hnp

/--
[wcd_cornerBalance_eq_neg_pivotSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_cornerBalance_eq_neg_pivotSum_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hpf : ∀ i < dartOrbitPeriod K a, ¬(wcd_frontCell ((dartNext K)^[i] a.1) ∈ K ∧ wcd_sideCell ((dartNext K)^[i] a.1) ∉ K)) :
-- imply
  cornerBalance K a = - ∑ i ∈ Finset.range (dartOrbitPeriod K a), defect (wcd_toVtxFinset K hK) (wcd_pivot ((dartNext K)^[i] a.1)) := by
-- proof
  apply StatMech.Wcd.wcd_cornerBalance_eq_neg_pivotSum K hK a hpf

/--
[wcd_pivotSum_eq_regVertsSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_pivotSum_eq_regVertsSum_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hinj : Set.InjOn (fun i => wcd_pivot ((dartNext K)^[i] a.1)) (Set.Iio (dartOrbitPeriod K a)))
  (hcov : ∀ v ∈ regVerts (wcd_toVtxFinset K hK), v ∉ (Finset.range (dartOrbitPeriod K a)).image (fun i => wcd_pivot ((dartNext K)^[i] a.1)) → defect (wcd_toVtxFinset K hK) v = 0) :
-- imply
  ∑ i ∈ Finset.range (dartOrbitPeriod K a), defect (wcd_toVtxFinset K hK) (wcd_pivot ((dartNext K)^[i] a.1)) = ∑ v ∈ regVerts (wcd_toVtxFinset K hK), defect (wcd_toVtxFinset K hK) v := by
-- proof
  apply StatMech.Wcd.wcd_pivotSum_eq_regVertsSum K hK a hinj hcov

/--
[wcd_cornerBalance_eq_neg_defectSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_cornerBalance_eq_neg_defectSum_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hbr : WcdPivotBridge K hK a) :
-- imply
  cornerBalance K a = - ∑ v ∈ regVerts (wcd_toVtxFinset K hK), defect (wcd_toVtxFinset K hK) v := by
-- proof
  apply StatMech.Wcd.wcd_cornerBalance_eq_neg_defectSum K hK a hbr

/--
[wcd_cornerBalance_eq_neg_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_cornerBalance_eq_neg_four_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hbr : WcdPivotBridge K hK a)
  (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
-- imply
  cornerBalance K a = -4 := by
-- proof
  apply StatMech.Wcd.wcd_cornerBalance_eq_neg_four K hK a hbr hbuild

/--
[wcd_revCount_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_revCount_eq_neg_one_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hbr : WcdPivotBridge K hK a)
  (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
-- imply
  revCount K a = -1 := by
-- proof
  apply StatMech.Wcd.wcd_revCount_eq_neg_one K hK a hbr hbuild

/--
[wcd_revCount_pm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_revCount_pm_one_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hbr : WcdPivotBridge K hK a)
  (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
-- imply
  revCount K a = 1 ∨ revCount K a = -1 := by
-- proof
  apply StatMech.Wcd.wcd_revCount_pm_one K hK a hbr hbuild

/--
[wcd_balanceIsFour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_balanceIsFour_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hbr : WcdPivotBridge K hK a)
  (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
-- imply
  BalanceIsFour K a := by
-- proof
  apply StatMech.Wcd.wcd_balanceIsFour K hK a hbr hbuild

/--
[wcd_unitCell_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_unitCell_finite_eq :
-- imply
  unitCell.Finite := by
-- proof
  apply StatMech.Wcd.wcd_unitCell_finite

/--
[wcd_toVtxFinset_unitCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_toVtxFinset_unitCell_eq
-- given
  (hfin : unitCell.Finite) :
-- imply
  wcd_toVtxFinset unitCell hfin = {((0 : ℤ), (0 : ℤ))} := by
-- proof
  apply StatMech.Wcd.wcd_toVtxFinset_unitCell hfin

/--
[wcd_witness_unitCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_witness_unitCell_eq :
-- imply
  cornerBalance unitCell ucBase = - ∑ v ∈ regVerts (wcd_toVtxFinset unitCell wcd_unitCell_finite), defect (wcd_toVtxFinset unitCell wcd_unitCell_finite) v := by
-- proof
  apply StatMech.Wcd.wcd_witness_unitCell

/--
[wcd_witness_pinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_witness_pinch_eq :
-- imply
  wad_n2d ({((0 : ℤ), (0 : ℤ)), (1, 1)} : Finset (ℤ × ℤ)) = 1 := by
-- proof
  apply StatMech.Wcd.wcd_witness_pinch

/--
[wcd_witness_unitSquare_defectSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcddefectbridge.lean)
-/
@[path]
private lemma wcd_witness_unitSquare_defectSum_eq :
-- imply
  ∑ v ∈ regVerts ({((0 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ)), defect ({((0 : ℤ), (0 : ℤ))} : Finset (ℤ × ℤ)) v = 4 := by
-- proof
  apply StatMech.Wcd.wcd_witness_unitSquare_defectSum


-- created on 2026-10-23
