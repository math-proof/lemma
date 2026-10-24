import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut
open Finset StatMech StatMech.FrontierD


/--
[sixVertexCutTorusArrows_horizontal_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean)
-/
@[path]
private lemma sixVertexCutTorusArrows_horizontal_zero_eq
  {T : EvenTorus}
  {ω : SixVertexArrows T}
  {j : Fin T.height} :
-- imply
  (sixVertexCutTorusArrows T ω).horizontal (0, j) = ω.horizontal (finLastOfPos T.width_pos, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexCutTorusArrows_horizontal_zero T ω j

/--
[sixVertexCutTorusArrows_horizontal_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean)
-/
@[path]
private lemma sixVertexCutTorusArrows_horizontal_succ_eq
  {T : EvenTorus}
  {ω : SixVertexArrows T}
  {i : Fin T.width}
  {j : Fin T.height} :
-- imply
  (sixVertexCutTorusArrows T ω).horizontal (i.succ, j) = ω.horizontal (i, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexCutTorusArrows_horizontal_succ T ω i j

/--
[sixVertexCutTorusArrows_horizontal_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean)
-/
@[path]
private lemma sixVertexCutTorusArrows_horizontal_last_eq
  {T : EvenTorus}
  {ω : SixVertexArrows T}
  {j : Fin T.height} :
-- imply
  (sixVertexCutTorusArrows T ω).horizontal (Fin.last T.width, j) = ω.horizontal (finLastOfPos T.width_pos, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexCutTorusArrows_horizontal_last T ω j

/--
[sixVertexCutTorusArrows_vertical_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean)
-/
@[path]
private lemma sixVertexCutTorusArrows_vertical_zero_eq
  {T : EvenTorus}
  {ω : SixVertexArrows T}
  {i : Fin T.width} :
-- imply
  (sixVertexCutTorusArrows T ω).vertical (i, 0) = ω.vertical (i, finLastOfPos T.height_pos) := by
-- proof
  apply StatMech.FrontierD.sixVertexCutTorusArrows_vertical_zero T ω i

/--
[sixVertexCutTorusArrows_vertical_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean)
-/
@[path]
private lemma sixVertexCutTorusArrows_vertical_succ_eq
  {T : EvenTorus}
  {ω : SixVertexArrows T}
  {i : Fin T.width}
  {j : Fin T.height} :
-- imply
  (sixVertexCutTorusArrows T ω).vertical (i, j.succ) = ω.vertical (i, j) := by
-- proof
  apply StatMech.FrontierD.sixVertexCutTorusArrows_vertical_succ T ω i j

/--
[sixVertexCutTorusArrows_vertical_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean)
-/
@[path]
private lemma sixVertexCutTorusArrows_vertical_last_eq
  {T : EvenTorus}
  {ω : SixVertexArrows T}
  {i : Fin T.width} :
-- imply
  (sixVertexCutTorusArrows T ω).vertical (i, Fin.last T.height) = ω.vertical (i, finLastOfPos T.height_pos) := by
-- proof
  apply StatMech.FrontierD.sixVertexCutTorusArrows_vertical_last T ω i

/--
[sixVertexCutTorusArrows_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean)
-/
@[path]
private lemma sixVertexCutTorusArrows_boundary_eq
  {T : EvenTorus}
  {ω : SixVertexArrows T} :
-- imply
  sixVertexRectangleBoundary (sixVertexCutTorusArrows T ω) = sixVertexToroidalRectangleBoundary (sixVertexTorusSeam T ω) := by
-- proof
  apply StatMech.FrontierD.sixVertexCutTorusArrows_boundary T ω

/--
[sixVertexGlue_cut_torus_arrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean)
-/
@[path]
private lemma sixVertexGlue_cut_torus_arrows_eq
  {T : EvenTorus}
  {ω : SixVertexArrows T} :
-- imply
  sixVertexGlueTorusArrows T (sixVertexCutTorusArrows T ω) = ω := by
-- proof
  apply StatMech.FrontierD.sixVertexGlue_cut_torus_arrows T ω

/--
[sixVertexCutTorusArrows_localWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean)
-/
@[path]
private lemma sixVertexCutTorusArrows_localWeight_eq
  {T : EvenTorus}
  {c : ℝ}
  {ω : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  (sixVertexCutTorusArrows T ω).localWeight c v = ω.localWeight c v := by
-- proof
  apply StatMech.FrontierD.sixVertexCutTorusArrows_localWeight T c ω v

/--
[sixVertexCutTorusArrows_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean)
-/
@[path]
private lemma sixVertexCutTorusArrows_weight_eq
  {T : EvenTorus}
  {c : ℝ}
  {ω : SixVertexArrows T} :
-- imply
  (sixVertexCutTorusArrows T ω).weight c = ω.weight c := by
-- proof
  apply StatMech.FrontierD.sixVertexCutTorusArrows_weight T c ω

/--
[sixVertexRectangleToroidalPartitionSum_eq_torusArrowPartitionSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean)
-/
@[path]
private lemma sixVertexRectangleToroidalPartitionSum_eq_torusArrowPartitionSum_eq
  {T : EvenTorus}
  {c : ℝ} :
-- imply
  sixVertexRectangleToroidalPartitionSum T.width T.height c = sixVertexTorusArrowPartitionSum T c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleToroidalPartitionSum_eq_torusArrowPartitionSum T c

/--
[sixVertexRectangleBalancedPartitionSum_le_torusArrowPartitionSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean)
-/
@[path]
private lemma sixVertexRectangleBalancedPartitionSum_le_torusArrowPartitionSum_eq
  {T : EvenTorus}
  {c : ℝ}
-- given
  (hc : 0 ≤ c) :
-- imply
  sixVertexRectangleBalancedPartitionSum T.width T.height c ≤ sixVertexTorusArrowPartitionSum T c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBalancedPartitionSum_le_torusArrowPartitionSum T hc

/--
[sixVertexTorusArrowPartitionSum_le_card_mul_maxBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean)
-/
@[path]
private lemma sixVertexTorusArrowPartitionSum_le_card_mul_maxBoundary_eq
  {T : EvenTorus}
  {c : ℝ} :
-- imply
  sixVertexTorusArrowPartitionSum T c ≤ (2 : ℝ) ^ (T.width + T.height) * sixVertexRectangleMaxToroidalBoundaryPartitionSum T.width T.height c := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusArrowPartitionSum_le_card_mul_maxBoundary T c


-- created on 2026-10-23
