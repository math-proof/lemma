import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.wadangledefect.Part4
open Finset StatMech.Euc StatMech StatMech.Wad


/--
[wad_mem_surround_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_mem_surround_iff_eq
  {v : Vtx}
  {c : Cell} :
-- imply
  c ∈ surroundCells v ↔ v ∈ cellVerts c := by
-- proof
  apply StatMech.Wad.wad_mem_surround_iff v c

/--
[wad_cellVerts_subset_regVerts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_cellVerts_subset_regVerts_eq
  {K : Finset Cell}
  {c : Cell}
-- given
  (hc : c ∈ K) :
-- imply
  cellVerts c ⊆ regVerts K := by
-- proof
  apply StatMech.Wad.wad_cellVerts_subset_regVerts hc

/--
[wad_cellVerts_inter_regVerts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_cellVerts_inter_regVerts_eq
  {K : Finset Cell}
  {c : Cell}
-- given
  (hc : c ∈ K) :
-- imply
  cellVerts c ∩ regVerts K = cellVerts c := by
-- proof
  apply StatMech.Wad.wad_cellVerts_inter_regVerts hc

/--
[wad_angleSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_angleSum_eq
  {K : Finset Cell} :
-- imply
  ∑ v ∈ regVerts K, cellDeg K v = 4 * K.card := by
-- proof
  apply StatMech.Wad.wad_angleSum K

/--
[wad_edge_not_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_edge_not_diag_eq
  {K : Finset Cell}
  {e : Sym2 Vtx}
-- given
  (he : e ∈ regEdges K) :
-- imply
  ¬ e.IsDiag := by
-- proof
  apply StatMech.Wad.wad_edge_not_diag he

/--
[wad_edge_mem_regVerts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_edge_mem_regVerts_eq
  {K : Finset Cell}
  {e : Sym2 Vtx}
  {v : Vtx}
-- given
  (he : e ∈ regEdges K)
  (hv : v ∈ e) :
-- imply
  v ∈ regVerts K := by
-- proof
  apply StatMech.Wad.wad_edge_mem_regVerts he hv

/--
[wad_endpoints_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_endpoints_card_eq
  {K : Finset Cell}
  {e : Sym2 Vtx}
-- given
  (he : e ∈ regEdges K) :
-- imply
  ((regVerts K).filter (fun v => v ∈ e)).card = 2 := by
-- proof
  apply StatMech.Wad.wad_endpoints_card he

/--
[wad_edgeSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_edgeSum_eq
  {K : Finset Cell} :
-- imply
  ∑ v ∈ regVerts K, edgeDeg K v = 2 * (regEdges K).card := by
-- proof
  apply StatMech.Wad.wad_edgeSum K

/--
[wad_defect_eq_four_chi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_defect_eq_four_chi_eq
  {K : Finset Cell} :
-- imply
  ∑ v ∈ regVerts K, defect K v = 4 * regChi K := by
-- proof
  apply StatMech.Wad.wad_defect_eq_four_chi K

/--
[wad_edge_incident_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_edge_incident_cases_eq
  {K : Finset Cell}
  {e : Sym2 Vtx}
  {v : Vtx}
-- given
  (he : e ∈ regEdges K)
  (hv : v ∈ e) :
-- imply
  e = incidentEdgeR v ∨ e = incidentEdgeL v ∨ e = incidentEdgeU v ∨ e = incidentEdgeD v := by
-- proof
  apply StatMech.Wad.wad_edge_incident_cases he hv

/--
[wad_incidentR_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_incidentR_mem_eq
  {K : Finset Cell}
  {v : Vtx} :
-- imply
  incidentEdgeR v ∈ regEdges K ↔ (v ∈ K ∨ (v.1, v.2 - 1) ∈ K) := by
-- proof
  apply StatMech.Wad.wad_incidentR_mem K v

/--
[wad_incidentL_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_incidentL_mem_eq
  {K : Finset Cell}
  {v : Vtx} :
-- imply
  incidentEdgeL v ∈ regEdges K ↔ ((v.1 - 1, v.2) ∈ K ∨ (v.1 - 1, v.2 - 1) ∈ K) := by
-- proof
  apply StatMech.Wad.wad_incidentL_mem K v

/--
[wad_incidentU_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_incidentU_mem_eq
  {K : Finset Cell}
  {v : Vtx} :
-- imply
  incidentEdgeU v ∈ regEdges K ↔ ((v.1 - 1, v.2) ∈ K ∨ v ∈ K) := by
-- proof
  apply StatMech.Wad.wad_incidentU_mem K v

/--
[wad_incidentD_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_incidentD_mem_eq
  {K : Finset Cell}
  {v : Vtx} :
-- imply
  incidentEdgeD v ∈ regEdges K ↔ ((v.1 - 1, v.2 - 1) ∈ K ∨ (v.1, v.2 - 1) ∈ K) := by
-- proof
  apply StatMech.Wad.wad_incidentD_mem K v

/--
[wad_v_mem_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_v_mem_incident_eq
  {v : Vtx} :
-- imply
  v ∈ incidentEdgeR v ∧ v ∈ incidentEdgeL v ∧ v ∈ incidentEdgeU v ∧ v ∈ incidentEdgeD v := by
-- proof
  apply StatMech.Wad.wad_v_mem_incident v

/--
[wad_edgeDeg_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_edgeDeg_eq_eq
  {K : Finset Cell}
  {v : Vtx} :
-- imply
  edgeDeg K v = (({incidentEdgeR v, incidentEdgeL v, incidentEdgeU v, incidentEdgeD v} : Finset (Sym2 Vtx)).filter (fun e => e ∈ regEdges K)).card := by
-- proof
  apply StatMech.Wad.wad_edgeDeg_eq K v

/--
[wad_defect_classify](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_defect_classify_eq
  {K : Finset Cell}
  {v : Vtx}
-- given
  (hv : v ∈ regVerts K) :
-- imply
  defect K v = 1 ∨ defect K v = 0 ∨ defect K v = -1 ∨ defect K v = -2 := by
-- proof
  apply StatMech.Wad.wad_defect_classify K v hv

/--
[wad_defectSum_eq_counts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_defectSum_eq_counts_eq
  {K : Finset Cell} :
-- imply
  ∑ v ∈ regVerts K, defect K v = wad_n1 K - wad_n3 K - 2 * wad_n2d K := by
-- proof
  apply StatMech.Wad.wad_defectSum_eq_counts K

/--
[wad_defect_eq_four_chi_counts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_defect_eq_four_chi_counts_eq
  {K : Finset Cell} :
-- imply
  wad_n1 K - wad_n3 K - 2 * wad_n2d K = 4 * regChi K := by
-- proof
  apply StatMech.Wad.wad_defect_eq_four_chi_counts K

/--
[wad_defect_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_defect_eq_four_eq
  {K : Finset Cell}
-- given
  (hK : EucBuildable K)
  (hpinch : wad_n2d K = 0) :
-- imply
  wad_n1 K - wad_n3 K = 4 := by
-- proof
  apply StatMech.Wad.wad_defect_eq_four hK hpinch

/--
[wad_n1_unitSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_n1_unitSquare_eq :
-- imply
  wad_n1 ({((0:ℤ),(0:ℤ))} : Finset Cell) = 4 := by
-- proof
  apply StatMech.Wad.wad_n1_unitSquare

/--
[wad_n3_unitSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_n3_unitSquare_eq :
-- imply
  wad_n3 ({((0:ℤ),(0:ℤ))} : Finset Cell) = 0 := by
-- proof
  apply StatMech.Wad.wad_n3_unitSquare

/--
[wad_n2d_unitSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_n2d_unitSquare_eq :
-- imply
  wad_n2d ({((0:ℤ),(0:ℤ))} : Finset Cell) = 0 := by
-- proof
  apply StatMech.Wad.wad_n2d_unitSquare

/--
[wad_witness_unitSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_witness_unitSquare_eq :
-- imply
  wad_n1 ({((0:ℤ),(0:ℤ))} : Finset Cell) - wad_n3 ({((0:ℤ),(0:ℤ))} : Finset Cell) = 4 := by
-- proof
  apply StatMech.Wad.wad_witness_unitSquare

/--
[wad_n2d_domino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_n2d_domino_eq :
-- imply
  wad_n2d ({((0:ℤ),(0:ℤ)),(1,0)} : Finset Cell) = 0 := by
-- proof
  apply StatMech.Wad.wad_n2d_domino

/--
[wad_witness_domino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_witness_domino_eq :
-- imply
  wad_n1 ({((0:ℤ),(0:ℤ)),(1,0)} : Finset Cell) - wad_n3 ({((0:ℤ),(0:ℤ)),(1,0)} : Finset Cell) = 4 := by
-- proof
  apply StatMech.Wad.wad_witness_domino

/--
[wad_n1_Ltromino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_n1_Ltromino_eq :
-- imply
  wad_n1 ({((0:ℤ),(0:ℤ)),(1,0),(0,1)} : Finset Cell) = 5 := by
-- proof
  apply StatMech.Wad.wad_n1_Ltromino

/--
[wad_n3_Ltromino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_n3_Ltromino_eq :
-- imply
  wad_n3 ({((0:ℤ),(0:ℤ)),(1,0),(0,1)} : Finset Cell) = 1 := by
-- proof
  apply StatMech.Wad.wad_n3_Ltromino

/--
[wad_n2d_Ltromino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_n2d_Ltromino_eq :
-- imply
  wad_n2d ({((0:ℤ),(0:ℤ)),(1,0),(0,1)} : Finset Cell) = 0 := by
-- proof
  apply StatMech.Wad.wad_n2d_Ltromino

/--
[wad_witness_Ltromino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_witness_Ltromino_eq :
-- imply
  wad_n1 ({((0:ℤ),(0:ℤ)),(1,0),(0,1)} : Finset Cell) - wad_n3 ({((0:ℤ),(0:ℤ)),(1,0),(0,1)} : Finset Cell) = 4 := by
-- proof
  apply StatMech.Wad.wad_witness_Ltromino

/--
[wad_witness_holeyRing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean)
-/
@[path]
private lemma wad_witness_holeyRing_eq :
-- imply
  wad_n1 ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)} : Finset Cell) - wad_n3 ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)} : Finset Cell) - 2 * wad_n2d ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)} : Finset Cell) = 0 := by
-- proof
  apply StatMech.Wad.wad_witness_holeyRing


-- created on 2026-10-23
