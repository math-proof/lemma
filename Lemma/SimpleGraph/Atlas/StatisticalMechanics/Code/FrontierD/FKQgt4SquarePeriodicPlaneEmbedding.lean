import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicPlaneEmbedding.Part5
open Set SimpleGraph StatMech StatMech.FrontierD


/--
[squareComplexPoint_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareComplexPoint_re_eq
  {x : Site 2} :
-- imply
  (squareComplexPoint x).re = x 0 := by
-- proof
  apply StatMech.FrontierD.squareComplexPoint_re x

/--
[squareComplexPoint_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareComplexPoint_im_eq
  {x : Site 2} :
-- imply
  (squareComplexPoint x).im = x 1 := by
-- proof
  apply StatMech.FrontierD.squareComplexPoint_im x

/--
[squareComplexPoint_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareComplexPoint_injective_eq :
-- imply
  Function.Injective squareComplexPoint := by
-- proof
  apply StatMech.FrontierD.squareComplexPoint_injective

/--
[squareComplexCoordinates_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareComplexCoordinates_zero_eq
  {z : Complex} :
-- imply
  squareComplexCoordinates z 0 = z.re := by
-- proof
  apply StatMech.FrontierD.squareComplexCoordinates_zero z

/--
[squareComplexCoordinates_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareComplexCoordinates_one_eq
  {z : Complex} :
-- imply
  squareComplexCoordinates z 1 = z.im := by
-- proof
  apply StatMech.FrontierD.squareComplexCoordinates_one z

/--
[squareOffsetVertex_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareOffsetVertex_apply_eq
  {offset : Complex}
  {x : Site 2} :
-- imply
  squareOffsetVertex offset x = squareComplexPoint x + offset := by
-- proof
  apply StatMech.FrontierD.squareOffsetVertex_apply offset x

/--
[squareOffsetVertex_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareOffsetVertex_shift_eq
  {offset : Complex}
  {z x : Site 2} :
-- imply
  squareOffsetVertex offset (siteTranslate z x) = squareOffsetVertex offset x + squareComplexPeriod z := by
-- proof
  apply StatMech.FrontierD.squareOffsetVertex_shift offset z x

/--
[squareOffsetVertex_proper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareOffsetVertex_proper_eq
  {offset : Complex}
  {R : Real} :
-- imply
  {x : Site 2 | ‖(squareOffsetVertex offset x : Complex)‖ ≤ R}.Finite := by
-- proof
  apply StatMech.FrontierD.squareOffsetVertex_proper offset R

/--
[squareOffsetEdgeArc_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareOffsetEdgeArc_injective_eq
  {offset : Complex}
  {x y : Site 2}
-- given
  (hxy : square.graph.Adj x y) :
-- imply
  Function.Injective (squareOffsetEdgeArc offset hxy) := by
-- proof
  apply StatMech.FrontierD.squareOffsetEdgeArc_injective offset hxy

/--
[squareOffsetEdgeArc_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareOffsetEdgeArc_symm_eq
  {offset : Complex}
  {x y : Site 2}
-- given
  (hxy : square.graph.Adj x y) :
-- imply
  Set.range (squareOffsetEdgeArc offset hxy.symm) = Set.range (squareOffsetEdgeArc offset hxy) := by
-- proof
  apply StatMech.FrontierD.squareOffsetEdgeArc_symm offset hxy

/--
[squareOffsetEdgeArc_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareOffsetEdgeArc_shift_eq
  {offset : Complex}
  {z : Site 2}
  {x y : Site 2}
-- given
  (hxy : square.graph.Adj x y) :
-- imply
  Set.range (squareOffsetEdgeArc offset ((square.shift_adj z x y).2 hxy)) = (fun p => p + squareComplexPeriod z) '' Set.range (squareOffsetEdgeArc offset hxy) := by
-- proof
  apply StatMech.FrontierD.squareOffsetEdgeArc_shift offset z hxy

/--
[squareSite_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareSite_eq_iff_eq
  {x y : Site 2} :
-- imply
  x = y ↔ x 0 = y 0 ∧ x 1 = y 1 := by
-- proof
  apply StatMech.FrontierD.squareSite_eq_iff x y

/--
[affineInt_mem_interval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma affineInt_mem_interval_eq
  {a b : Int}
  {t : unitInterval} :
-- imply
  ((min a b : Int) : Real) ≤ (t : Real) * (b - a) + a ∧ (t : Real) * (b - a) + a ≤ ((max a b : Int) : Real) := by
-- proof
  apply StatMech.FrontierD.affineInt_mem_interval a b t

/--
[squareOffsetSegment_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareOffsetSegment_re_eq
  {offset : Complex}
  {x y : Site 2}
  {t : unitInterval} :
-- imply
  (Path.segment (squareOffsetVertex offset x) (squareOffsetVertex offset y) t).re = (t : Real) * ((y 0 : Real) - (x 0 : Real)) + (x 0 : Real) + offset.re := by
-- proof
  apply StatMech.FrontierD.squareOffsetSegment_re offset x y t

/--
[squareOffsetSegment_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareOffsetSegment_im_eq
  {offset : Complex}
  {x y : Site 2}
  {t : unitInterval} :
-- imply
  (Path.segment (squareOffsetVertex offset x) (squareOffsetVertex offset y) t).im = (t : Real) * ((y 1 : Real) - (x 1 : Real)) + (x 1 : Real) + offset.im := by
-- proof
  apply StatMech.FrontierD.squareOffsetSegment_im offset x y t

/--
[squareEdges_commonEndpoint_of_box_overlap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareEdges_commonEndpoint_of_box_overlap_eq
  {x y z w : Site 2}
-- given
  (hxy : square.graph.Adj x y)
  (hzw : square.graph.Adj z w)
  (h00 : min (x 0) (y 0) ≤ max (z 0) (w 0))
  (h01 : min (z 0) (w 0) ≤ max (x 0) (y 0))
  (h10 : min (x 1) (y 1) ≤ max (z 1) (w 1))
  (h11 : min (z 1) (w 1) ≤ max (x 1) (y 1)) :
-- imply
  x = z ∨ x = w ∨ y = z ∨ y = w := by
-- proof
  apply StatMech.FrontierD.squareEdges_commonEndpoint_of_box_overlap hxy hzw h00 h01 h10 h11

/--
[squareNeighborSegments_inter_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareNeighborSegments_inter_eq_eq
  {offset : Complex}
  {v a b : Site 2}
  {p : Complex}
-- given
  (hva : square.graph.Adj v a)
  (hvb : square.graph.Adj v b)
  (hab : a ≠ b)
  (hpa : p ∈ Set.range (Path.segment (squareOffsetVertex offset v) (squareOffsetVertex offset a)))
  (hpb : p ∈ Set.range (Path.segment (squareOffsetVertex offset v) (squareOffsetVertex offset b))) :
-- imply
  p = squareOffsetVertex offset v := by
-- proof
  apply StatMech.FrontierD.squareNeighborSegments_inter_eq offset hva hvb hab hpa hpb

/--
[mem_range_squareOffsetSegment_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma mem_range_squareOffsetSegment_symm_eq
  {offset : Complex}
  {x y : Site 2}
  {p : Complex}
-- given
  (hp : p ∈ Set.range (Path.segment (squareOffsetVertex offset x) (squareOffsetVertex offset y))) :
-- imply
  p ∈ Set.range (Path.segment (squareOffsetVertex offset y) (squareOffsetVertex offset x)) := by
-- proof
  apply StatMech.FrontierD.mem_range_squareOffsetSegment_symm offset x y hp

/--
[squareOffsetEdgeArc_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareOffsetEdgeArc_intersection_eq
  {offset : Complex}
  {x y z w : Site 2}
  {p : Complex}
-- given
  (hxy : square.graph.Adj x y)
  (hzw : square.graph.Adj z w)
  (hne : s(x, y) ≠ s(z, w))
  (hp : p ∈ Set.range (squareOffsetEdgeArc offset hxy))
  (hq : p ∈ Set.range (squareOffsetEdgeArc offset hzw)) :
-- imply
  ∃ v, (v = x ∨ v = y) ∧ (v = z ∨ v = w) ∧ squareOffsetVertex offset v = p := by
-- proof
  apply StatMech.FrontierD.squareOffsetEdgeArc_intersection offset hxy hzw p hne hp hq

/--
[squareOffsetEdgeArc_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareOffsetEdgeArc_disjoint_eq
  {offset : Complex}
  {x y z w : Site 2}
-- given
  (hxy : square.graph.Adj x y)
  (hzw : square.graph.Adj z w)
  (hxz : x ≠ z)
  (hxw : x ≠ w)
  (hyz : y ≠ z)
  (hyw : y ≠ w) :
-- imply
  Disjoint (Set.range (squareOffsetEdgeArc offset hxy)) (Set.range (squareOffsetEdgeArc offset hzw)) := by
-- proof
  apply StatMech.FrontierD.squareOffsetEdgeArc_disjoint offset hxy hzw hxz hxw hyz hyw

/--
[squareOffsetVertex_sub_norm_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareOffsetVertex_sub_norm_of_adj_eq
  {offset : Complex}
  {x y : Site 2}
-- given
  (hxy : square.graph.Adj x y) :
-- imply
  ‖(squareOffsetVertex offset x : Complex) - squareOffsetVertex offset y‖ = 1 := by
-- proof
  apply StatMech.FrontierD.squareOffsetVertex_sub_norm_of_adj offset hxy

/--
[squareOffsetVertex_sub_segment_norm_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareOffsetVertex_sub_segment_norm_le_one_eq
  {offset : Complex}
  {x y : Site 2}
  {t : unitInterval}
-- given
  (hxy : square.graph.Adj x y) :
-- imply
  ‖(squareOffsetVertex offset x : Complex) - Path.segment (squareOffsetVertex offset x) (squareOffsetVertex offset y) t‖ ≤ 1 := by
-- proof
  apply StatMech.FrontierD.squareOffsetVertex_sub_segment_norm_le_one offset hxy t

/--
[squareOffsetEndpoint_norm_le_of_mem_segment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareOffsetEndpoint_norm_le_of_mem_segment_eq
  {offset : Complex}
  {x y : Site 2}
  {p : Complex}
-- given
  (hxy : square.graph.Adj x y)
  (hp : p ∈ Set.range (Path.segment (squareOffsetVertex offset x) (squareOffsetVertex offset y))) :
-- imply
  ‖(squareOffsetVertex offset x : Complex)‖ ≤ ‖p‖ + 1 := by
-- proof
  apply StatMech.FrontierD.squareOffsetEndpoint_norm_le_of_mem_segment offset hxy hp

/--
[squareOffsetEdgeArc_locallyFinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquarePeriodicPlaneEmbedding.lean)
-/
@[path]
private lemma squareOffsetEdgeArc_locallyFinite_eq
  {offset : Complex}
  {K : Set Complex}
-- given
  (hK : IsCompact K) :
-- imply
  {xy : Site 2 × Site 2 | ∃ hxy : square.graph.Adj xy.1 xy.2, (Set.range (squareOffsetEdgeArc offset hxy) ∩ K).Nonempty}.Finite := by
-- proof
  apply StatMech.FrontierD.squareOffsetEdgeArc_locallyFinite offset K hK


-- created on 2026-10-23
