import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectCyclicPred_iterate_zero_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectCyclicPred_iterate_zero_val_eq
  {N : Nat}
  {n : Nat}
-- given
  (hN : 0 < N)
  (hn : n <= N) :
-- imply
  ((SixVertexArrows.cyclicPred hN)^[n] (⟨0, hN⟩ : Fin N)).val = if n = 0 then 0 else N - n := by
-- proof
  apply StatMech.FrontierD.fkRectCyclicPred_iterate_zero_val hN n hn

/--
[fkRectCyclicPred_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectCyclicPred_val_eq
  {N : Nat}
  {i : Fin N}
-- given
  (hN : 0 < N) :
-- imply
  (SixVertexArrows.cyclicPred hN i).val = if i.val = 0 then N - 1 else i.val - 1 := by
-- proof
  apply StatMech.FrontierD.fkRectCyclicPred_val hN i

/--
[fkRectFullOpenGraph_adj_verticalPred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectFullOpenGraph_adj_verticalPred_eq
  {R : FKRectTorus}
  {x : Fin R.width}
  {y : Fin R.height} :
-- imply
  (fkRectFullOpenGraph R).Adj (x, y) (x, SixVertexArrows.cyclicPred R.height_pos y) := by
-- proof
  apply StatMech.FrontierD.fkRectFullOpenGraph_adj_verticalPred R x y

/--
[fkRectFullOpenGraph_adj_horizontalPred_diag_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectFullOpenGraph_adj_horizontalPred_diag_zero_eq
  {R : FKRectTorus}
  {x : Fin R.width} :
-- imply
  (fkRectFullOpenGraph R).Adj (x, (⟨0, R.height_pos⟩ : Fin R.height)) (SixVertexArrows.cyclicPred R.width_pos x, SixVertexArrows.cyclicPred R.height_pos (⟨0, R.height_pos⟩ : Fin R.height)) := by
-- proof
  apply StatMech.FrontierD.fkRectFullOpenGraph_adj_horizontalPred_diag_zero R x

/--
[fkRectHorizontalSeamIncrement_same_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectHorizontalSeamIncrement_same_fst_eq
  {R : FKRectTorus}
  {x : Fin R.width}
  {y z : Fin R.height} :
-- imply
  fkRectHorizontalSeamIncrement R (x, y) (x, z) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalSeamIncrement_same_fst R x y z

/--
[fkRectVerticalSeamIncrement_same_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectVerticalSeamIncrement_same_snd_eq
  {R : FKRectTorus}
  {x z : Fin R.width}
  {y : Fin R.height} :
-- imply
  fkRectVerticalSeamIncrement R (x, y) (z, y) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalSeamIncrement_same_snd R x z y

/--
[fkRectHorizontalSeamIncrement_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectHorizontalSeamIncrement_pred_eq
  {R : FKRectTorus}
  {x : Fin R.width}
  {y z : Fin R.height} :
-- imply
  fkRectHorizontalSeamIncrement R (x, y) (SixVertexArrows.cyclicPred R.width_pos x, z) = if x.val = 0 then -1 else 0 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalSeamIncrement_pred R x y z

/--
[fkRectVerticalSeamIncrement_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectVerticalSeamIncrement_pred_eq
  {R : FKRectTorus}
  {x z : Fin R.width}
  {y : Fin R.height} :
-- imply
  fkRectVerticalSeamIncrement R (x, y) (z, SixVertexArrows.cyclicPred R.height_pos y) = if y.val = 0 then -1 else 0 := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalSeamIncrement_pred R x z y

/--
[fkRectVerticalSeamIncrement_pred_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectVerticalSeamIncrement_pred_zero_eq
  {R : FKRectTorus}
  {x z : Fin R.width} :
-- imply
  fkRectVerticalSeamIncrement R (x, (⟨0, R.height_pos⟩ : Fin R.height)) (z, SixVertexArrows.cyclicPred R.height_pos (⟨0, R.height_pos⟩ : Fin R.height)) = -1 := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalSeamIncrement_pred_zero R x z

/--
[fkRectVerticalSeamIncrement_pred_zero_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectVerticalSeamIncrement_pred_zero_reverse_eq
  {R : FKRectTorus}
  {x z : Fin R.width} :
-- imply
  fkRectVerticalSeamIncrement R (z, SixVertexArrows.cyclicPred R.height_pos (⟨0, R.height_pos⟩ : Fin R.height)) (x, (⟨0, R.height_pos⟩ : Fin R.height)) = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalSeamIncrement_pred_zero_reverse R x z

/--
[fkRectWalkWinding_concat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectWalkWinding_concat_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {u v w : R.Vertex}
  {p : G.Walk u v}
-- given
  (h : G.Adj v w) :
-- imply
  fkRectWalkWinding R (p.concat h) = ((fkRectWalkWinding R p).1 + fkRectHorizontalSeamIncrement R v w, (fkRectWalkWinding R p).2 + fkRectVerticalSeamIncrement R v w) := by
-- proof
  apply StatMech.FrontierD.fkRectWalkWinding_concat R p h

/--
[fkRectVerticalFundamentalWalkAux_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectVerticalFundamentalWalkAux_winding_eq
  {R : FKRectTorus}
  {x : Fin R.width}
  {n : Nat}
-- given
  (hn : n <= R.height) :
-- imply
  fkRectWalkWinding R (fkRectVerticalFundamentalWalkAux R x (⟨0, R.height_pos⟩ : Fin R.height) n) = (0, if n = 0 then 0 else -1) := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalFundamentalWalkAux_winding R x n hn

/--
[fkRectHorizontalFundamentalWalkAux_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectHorizontalFundamentalWalkAux_winding_eq
  {R : FKRectTorus}
  {n : Nat}
-- given
  (hn : n <= R.width) :
-- imply
  fkRectWalkWinding R (fkRectHorizontalFundamentalWalkAux R (⟨0, R.width_pos⟩ : Fin R.width) n) = (if n = 0 then 0 else -1, 0) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalFundamentalWalkAux_winding R n hn

/--
[fkRectCyclicPred_iterate_zero_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectCyclicPred_iterate_zero_card_eq
  {N : Nat}
-- given
  (hN : 0 < N) :
-- imply
  (SixVertexArrows.cyclicPred hN)^[N] (⟨0, hN⟩ : Fin N) = (⟨0, hN⟩ : Fin N) := by
-- proof
  apply StatMech.FrontierD.fkRectCyclicPred_iterate_zero_card hN

/--
[fkRectWalkWinding_copy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectWalkWinding_copy_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {u v u' v' : R.Vertex}
  {p : G.Walk u v}
-- given
  (hu : u = u')
  (hv : v = v') :
-- imply
  fkRectWalkWinding R (p.copy hu hv) = fkRectWalkWinding R p := by
-- proof
  apply StatMech.FrontierD.fkRectWalkWinding_copy R p hu hv

/--
[fkRectHorizontalFundamentalWalk_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectHorizontalFundamentalWalk_winding_eq
  {R : FKRectTorus} :
-- imply
  fkRectWalkWinding R (fkRectHorizontalFundamentalWalk R) = (-1, 0) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalFundamentalWalk_winding R

/--
[fkRectVerticalFundamentalWalk_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectVerticalFundamentalWalk_winding_eq
  {R : FKRectTorus} :
-- imply
  fkRectWalkWinding R (fkRectVerticalFundamentalWalk R) = (0, -1) := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalFundamentalWalk_winding R

/--
[FKRectHasNet_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma FKRectHasNet_univ_eq
  {R : FKRectTorus} :
-- imply
  FKRectHasNet R (fkRectConfigurationOfEdges R Finset.univ) := by
-- proof
  apply StatMech.FrontierD.FKRectHasNet_univ R

/--
[fkRectNetIndicator_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean)
-/
@[path]
private lemma fkRectNetIndicator_univ_eq
  {R : FKRectTorus} :
-- imply
  fkRectNetIndicator R (fkRectConfigurationOfEdges R Finset.univ) = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectNetIndicator_univ R


-- created on 2026-10-23
