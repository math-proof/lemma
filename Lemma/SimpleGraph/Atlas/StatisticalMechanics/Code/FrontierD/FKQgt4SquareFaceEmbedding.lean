import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceEmbedding.Part3
open Set SimpleGraph StatMech StatMech.FrontierD


/--
[fkSquareBoxPlanar_imageGraph_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceEmbedding.lean)
-/
@[path]
private lemma fkSquareBoxPlanar_imageGraph_adj_iff_eq
  {m : Nat}
  {x y : Site 2} :
-- imply
  (imageGraph (fkSquareBoxPlanar m)).Adj x y ↔ x ∈ box 2 m ∧ y ∈ box 2 m ∧ (hypercubicLattice 2).Adj x y := by
-- proof
  apply StatMech.FrontierD.fkSquareBoxPlanar_imageGraph_adj_iff m x y

/--
[sharedPrimalEdge_mem_fkSquareBoxPlanar_of_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceEmbedding.lean)
-/
@[path]
private lemma sharedPrimalEdge_mem_fkSquareBoxPlanar_of_inner_eq
  {N m : Nat}
  {f g : Site 2}
-- given
  (hNm : N < m)
  (hf : f ∈ box 2 N)
  (hfg : (hypercubicLattice 2).Adj f g) :
-- imply
  sharedPrimalEdge f g ∈ (imageGraph (fkSquareBoxPlanar m)).edgeSet := by
-- proof
  apply StatMech.FrontierD.sharedPrimalEdge_mem_fkSquareBoxPlanar_of_inner hNm hf hfg

/--
[fkSquareBox_innerFace_neighborSet_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceEmbedding.lean)
-/
@[path]
private lemma fkSquareBox_innerFace_neighborSet_eq_empty_eq
  {N m : Nat}
  {f : Site 2}
-- given
  (hNm : N < m)
  (hf : f ∈ box 2 N) :
-- imply
  (whb_faceRegion (imageGraph (fkSquareBoxPlanar m))).neighborSet f = ∅ := by
-- proof
  apply StatMech.FrontierD.fkSquareBox_innerFace_neighborSet_eq_empty hNm f hf

/--
[pfdFace_eq_inner_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceEmbedding.lean)
-/
@[path]
private lemma pfdFace_eq_inner_iff_eq
  {N m : Nat}
  {f g : Site 2}
-- given
  (hNm : N < m)
  (hg : g ∈ box 2 N) :
-- imply
  pfdFace (fkSquareBoxPlanar m) f = pfdFace (fkSquareBoxPlanar m) g ↔ f = g := by
-- proof
  apply StatMech.FrontierD.pfdFace_eq_inner_iff hNm hg

/--
[fkSquareBox_innerFaceMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceEmbedding.lean)
-/
@[path]
private lemma fkSquareBox_innerFaceMap_injective_eq
  {N m : Nat}
-- given
  (hNm : N < m) :
-- imply
  Function.Injective (fkSquareBox_innerFaceMap N m) := by
-- proof
  apply StatMech.FrontierD.fkSquareBox_innerFaceMap_injective hNm

/--
[fkSquareBox_innerFaceMap_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceEmbedding.lean)
-/
@[path]
private lemma fkSquareBox_innerFaceMap_adj_eq
  {N m : Nat}
  {x y : FK.boxVerts 2 N}
-- given
  (hNm : N < m) :
-- imply
  (FK.boxGraph 2 N).Adj x y ↔ (fkSquareBoxFullDualGraph m).Adj (fkSquareBox_innerFaceMap N m x) (fkSquareBox_innerFaceMap N m y) := by
-- proof
  apply StatMech.FrontierD.fkSquareBox_innerFaceMap_adj hNm x y

/--
[fkSquareBox_innerFaceMap_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceEmbedding.lean)
-/
@[path]
private lemma fkSquareBox_innerFaceMap_adjMatch_eq
  {N m : Nat}
-- given
  (hNm : N < m) :
-- imply
  ocd_AdjMatch (FK.boxGraph 2 N) (fkSquareBoxFullDualGraph m) (fkSquareBox_innerFaceMap N m) := by
-- proof
  apply StatMech.FrontierD.fkSquareBox_innerFaceMap_adjMatch hNm

/--
[fkSquareBox_boundary_of_outsideGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceEmbedding.lean)
-/
@[path]
private lemma fkSquareBox_boundary_of_outsideGraph_adj_eq
  {N m : Nat}
  {psi : ConfigSpace (Sym2 (kwg_Face (fkSquareBoxPlanar m)))}
  {x : FK.boxVerts 2 N}
  {z : kwg_Face (fkSquareBoxPlanar m)}
-- given
  (hNm : N < m)
  (hN : 1 ≤ N)
  (h : (ocd_outsideGraph (fkSquareBoxFullDualGraph m) (fkSquareBox_innerFaceMap N m) (fun _ => False) psi).Adj (fkSquareBox_innerFaceMap N m x) z) :
-- imply
  FK.boxBoundary 2 N x := by
-- proof
  apply StatMech.FrontierD.fkSquareBox_boundary_of_outsideGraph_adj hNm hN psi h

/--
[fkSquareBox_inducedWiring_le_boundaryClique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceEmbedding.lean)
-/
@[path]
private lemma fkSquareBox_inducedWiring_le_boundaryClique_eq
  {N m : Nat}
  {psi : ConfigSpace (Sym2 (kwg_Face (fkSquareBoxPlanar m)))}
-- given
  (hNm : N < m)
  (hN : 1 ≤ N) :
-- imply
  ocd_inducedWiring (fkSquareBoxFullDualGraph m) (fkSquareBox_innerFaceMap N m) (fun _ => False) psi ≤ boundaryCliqueGraph (FK.boxBoundary 2 N) := by
-- proof
  apply StatMech.FrontierD.fkSquareBox_inducedWiring_le_boundaryClique hNm hN psi


-- created on 2026-10-23
