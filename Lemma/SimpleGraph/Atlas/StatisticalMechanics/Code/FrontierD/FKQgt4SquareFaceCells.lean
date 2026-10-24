import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFaceCells
open Set SimpleGraph StatMech StatMech.FrontierD


/--
[fkSquareInteriorFace_corners_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceCells.lean)
-/
@[path]
private lemma fkSquareInteriorFace_corners_mem_box_eq
  {n : Nat}
  {a b : Int}
-- given
  (hf : fkSquareInteriorFace n ![a, b]) :
-- imply
  faceCorner00 a b ∈ box 2 n ∧ faceCorner10 a b ∈ box 2 n ∧ faceCorner11 a b ∈ box 2 n ∧ faceCorner01 a b ∈ box 2 n := by
-- proof
  apply StatMech.FrontierD.fkSquareInteriorFace_corners_mem_box hf

/--
[fkSquareBox_imageGraph_edge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceCells.lean)
-/
@[path]
private lemma fkSquareBox_imageGraph_edge_mem_eq
  {n : Nat}
  {x y : Site 2}
-- given
  (hx : x ∈ box 2 n)
  (hy : y ∈ box 2 n)
  (hxy : (hypercubicLattice 2).Adj x y) :
-- imply
  s(x, y) ∈ (imageGraph (fkSquareBoxPlanar n)).edgeSet := by
-- proof
  apply StatMech.FrontierD.fkSquareBox_imageGraph_edge_mem n hx hy hxy

/--
[fkSquareInteriorFace_sharedPrimalEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceCells.lean)
-/
@[path]
private lemma fkSquareInteriorFace_sharedPrimalEdge_mem_eq
  {n : Nat}
  {f g : Site 2}
-- given
  (hf : fkSquareInteriorFace n f)
  (hfg : (hypercubicLattice 2).Adj f g) :
-- imply
  sharedPrimalEdge f g ∈ (imageGraph (fkSquareBoxPlanar n)).edgeSet := by
-- proof
  apply StatMech.FrontierD.fkSquareInteriorFace_sharedPrimalEdge_mem hf hfg

/--
[fkSquareInteriorFace_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceCells.lean)
-/
@[path]
private lemma fkSquareInteriorFace_isolated_eq
  {n : Nat}
  {f : Site 2}
  {g : Site 2}
-- given
  (hf : fkSquareInteriorFace n f) :
-- imply
  ¬ (whb_faceRegion (imageGraph (fkSquareBoxPlanar n))).Adj f g := by
-- proof
  apply StatMech.FrontierD.fkSquareInteriorFace_isolated hf g

/--
[fkSquareInteriorFace_component_supp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceCells.lean)
-/
@[path]
private lemma fkSquareInteriorFace_component_supp_eq
  {n : Nat}
  {f : Site 2}
-- given
  (hf : fkSquareInteriorFace n f) :
-- imply
  ((whb_faceRegion (imageGraph (fkSquareBoxPlanar n))).connectedComponentMk f).supp = {f} := by
-- proof
  apply StatMech.FrontierD.fkSquareInteriorFace_component_supp hf

/--
[pfdFace_injective_on_fkSquareInteriorFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareFaceCells.lean)
-/
@[path]
private lemma pfdFace_injective_on_fkSquareInteriorFace_eq
  {n : Nat}
  {f g : Site 2}
-- given
  (hf : fkSquareInteriorFace n f)
  (hfg : pfdFace (fkSquareBoxPlanar n) f = pfdFace (fkSquareBoxPlanar n) g) :
-- imply
  f = g := by
-- proof
  apply StatMech.FrontierD.pfdFace_injective_on_fkSquareInteriorFace n hf hfg


-- created on 2026-10-23
