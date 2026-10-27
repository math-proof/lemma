import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding.Part7
open MeasureTheory StatMech.Lattice StatMech.Percolation SimpleGraph StatMech StatMech.FrontierD


/--
[hypercubicLattice_two_adj_add_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean)
-/
@[path]
private lemma hypercubicLattice_two_adj_add_left_eq
  {a x y : Site 2} :
-- imply
  (hypercubicLattice 2).Adj (a + x) (a + y) ↔ (hypercubicLattice 2).Adj x y := by
-- proof
  apply StatMech.FrontierD.hypercubicLattice_two_adj_add_left a x y

/--
[fkRectCutGraph_adj_of_torusAdj_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean)
-/
@[path]
private lemma fkRectCutGraph_adj_of_torusAdj_of_pos_eq
  {R : FKRectTorus}
  {x y : R.Vertex}
-- given
  (hxcol : 0 < x.1.val)
  (hycol : 0 < y.1.val)
  (hxrow : 0 < x.2.val)
  (hyrow : 0 < y.2.val)
  (hxy : (fkRectTorusGraph R).Adj x y) :
-- imply
  (fkRectCutGraph R).Adj x y := by
-- proof
  apply StatMech.FrontierD.fkRectCutGraph_adj_of_torusAdj_of_pos R x y hxcol hycol hxrow hyrow hxy

/--
[fkRectSquareRepresentativeVertex_vertexSquarePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean)
-/
@[path]
private lemma fkRectSquareRepresentativeVertex_vertexSquarePoint_eq
  {R : FKRectTorus}
  {x : R.Vertex} :
-- imply
  fkRectSquareRepresentativeVertex R (fkRectVertexSquarePoint R x) = x := by
-- proof
  apply StatMech.FrontierD.fkRectSquareRepresentativeVertex_vertexSquarePoint R x

/--
[fkRectReflectedDiagonalSite_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean)
-/
@[path]
private lemma fkRectReflectedDiagonalSite_mem_box_eq
  {s m : Nat}
-- given
  (hsm : s <= m) :
-- imply
  fkRectReflectedDiagonalSite s ∈ box 2 m := by
-- proof
  apply StatMech.FrontierD.fkRectReflectedDiagonalSite_mem_box hsm

/--
[fkRectPositiveDiagonalSite_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean)
-/
@[path]
private lemma fkRectPositiveDiagonalSite_mem_box_eq
  {s m : Nat}
-- given
  (hsm : s <= m) :
-- imply
  fkRectPositiveDiagonalSite s ∈ box 2 m := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveDiagonalSite_mem_box hsm

/--
[fk_twoPointFun_eq_connProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean)
-/
@[path]
private lemma fk_twoPointFun_eq_connProb_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : Real}
  {x y : V} :
-- imply
  FK.twoPointFun G p q x y = FK.connProb G p q x y := by
-- proof
  apply StatMech.FrontierD.fk_twoPointFun_eq_connProb G p q x y

/--
[fkRectLocalBox_twoPoint_reflectedDiagonal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean)
-/
@[path]
private lemma fkRectLocalBox_twoPoint_reflectedDiagonal_eq_eq
  {m s : Nat}
  {p q : Real}
-- given
  (hsm : s <= m) :
-- imply
  FK.twoPointFun (FK.boxGraph 2 m) p q (fkRectLocalBoxOrigin m) (fkRectLocalBoxReflectedDiagonal s m hsm) = FK.twoPointFun (FK.boxGraph 2 m) p q (fkRectLocalBoxOrigin m) (fkRectLocalBoxPositiveDiagonal s m hsm) := by
-- proof
  apply StatMech.FrontierD.fkRectLocalBox_twoPoint_reflectedDiagonal_eq m s hsm p q

/--
[fkRectLocalBoxVertex_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean)
-/
@[path]
private lemma fkRectLocalBoxVertex_origin_eq
  {R : FKRectTorus}
  {center : R.Vertex} :
-- imply
  fkRectLocalBoxVertex R center (origin 2) = center := by
-- proof
  apply StatMech.FrontierD.fkRectLocalBoxVertex_origin R center

/--
[fkRectLocalBoxVertex_reflectedDiagonal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean)
-/
@[path]
private lemma fkRectLocalBoxVertex_reflectedDiagonal_eq_eq
  {R : FKRectTorus}
  {center target : R.Vertex}
  {s : Nat}
-- given
  (hstep : fkRectVertexSquarePoint R target - fkRectVertexSquarePoint R center = ((s : Int), -(s : Int))) :
-- imply
  fkRectLocalBoxVertex R center (fkRectReflectedDiagonalSite s) = target := by
-- proof
  apply StatMech.FrontierD.fkRectLocalBoxVertex_reflectedDiagonal_eq R center target s hstep

/--
[fkRectLocalBoxFits_of_margin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean)
-/
@[path]
private lemma fkRectLocalBoxFits_of_margin_eq
  {R : FKRectTorus}
  {center : R.Vertex}
  {m cut lower upper : Nat}
-- given
  (hupper : upper < R.height)
  (hcolLower : cut + 2 * m <= center.1.val)
  (hcolUpper : center.1.val + 2 * m < R.width)
  (hrowLower : lower + 2 * m <= center.2.val)
  (hrowUpper : center.2.val + 2 * m <= upper) :
-- imply
  FKRectLocalBoxFits R center m cut lower upper := by
-- proof
  apply StatMech.FrontierD.fkRectLocalBoxFits_of_margin R center m cut lower upper hupper hcolLower hcolUpper hrowLower hrowUpper

/--
[fkRectSquareSiteOfPair_localBoxPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean)
-/
@[path]
private lemma fkRectSquareSiteOfPair_localBoxPoint_eq
  {R : FKRectTorus}
  {center : R.Vertex}
  {z : Site 2} :
-- imply
  fkRectSquareSiteOfPair (fkRectLocalBoxPoint R center z) = fkRectVertexSquareSite R center + z := by
-- proof
  apply StatMech.FrontierD.fkRectSquareSiteOfPair_localBoxPoint R center z

/--
[fkRectVertexSquarePoint_localBoxVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean)
-/
@[path]
private lemma fkRectVertexSquarePoint_localBoxVertex_eq
  {R : FKRectTorus}
  {center : R.Vertex}
  {m cut lower upper : Nat}
  {z : FK.boxVerts 2 m}
-- given
  (hfit : FKRectLocalBoxFits R center m cut lower upper) :
-- imply
  fkRectVertexSquarePoint R (fkRectLocalBoxVertex R center z) = fkRectLocalBoxPoint R center z := by
-- proof
  apply StatMech.FrontierD.fkRectVertexSquarePoint_localBoxVertex R center m cut lower upper hfit z

/--
[fkRectLocalBoxEmbedding_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean)
-/
@[path]
private lemma fkRectLocalBoxEmbedding_injective_eq
  {R : FKRectTorus}
  {center : R.Vertex}
  {m cut lower upper : Nat}
-- given
  (hfit : FKRectLocalBoxFits R center m cut lower upper) :
-- imply
  Function.Injective (fkRectLocalBoxEmbedding R center m cut lower upper hfit) := by
-- proof
  apply StatMech.FrontierD.fkRectLocalBoxEmbedding_injective R center m cut lower upper hfit

/--
[fkRectLocalBoxEmbedding_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean)
-/
@[path]
private lemma fkRectLocalBoxEmbedding_adjMatch_eq
  {R : FKRectTorus}
  {center : R.Vertex}
  {m cut lower upper : Nat}
-- given
  (hcut : 1 <= cut)
  (hlower : 1 <= lower)
  (hfit : FKRectLocalBoxFits R center m cut lower upper) :
-- imply
  FK.ocd_AdjMatch (FK.boxGraph 2 m) (fkRectInducedGraph R (fkRectRightStripBand R cut lower upper)) (fkRectLocalBoxEmbedding R center m cut lower upper hfit) := by
-- proof
  apply StatMech.FrontierD.fkRectLocalBoxEmbedding_adjMatch R center m cut lower upper hcut hlower hfit

/--
[fkRectLocalBox_twoPoint_le_strip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean)
-/
@[path]
private lemma fkRectLocalBox_twoPoint_le_strip_eq
  {R : FKRectTorus}
  {center : R.Vertex}
  {m cut lower upper : Nat}
  {p q : Real}
  {x y : FK.boxVerts 2 m}
-- given
  (hcut : 1 <= cut)
  (hlower : 1 <= lower)
  (hfit : FKRectLocalBoxFits R center m cut lower upper)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  FK.twoPointFun (FK.boxGraph 2 m) p q x y <= FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut lower upper)) p q (fkRectLocalBoxEmbedding R center m cut lower upper hfit x) (fkRectLocalBoxEmbedding R center m cut lower upper hfit y) := by
-- proof
  apply StatMech.FrontierD.fkRectLocalBox_twoPoint_le_strip R center m cut lower upper hcut hlower hfit hp hp1 hq x y


-- created on 2026-10-23
