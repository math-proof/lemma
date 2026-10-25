import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAxisStaircase.Part2
open StatMech StatMech.FrontierA


/--
[kwHorizontalPart_add_verticalPart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean)
-/
@[path]
private lemma kwHorizontalPart_add_verticalPart_eq
  {z : ℂ} :
-- imply
  kwHorizontalPart z + kwVerticalPart z = z := by
-- proof
  apply StatMech.FrontierA.kwHorizontalPart_add_verticalPart z

/--
[kwHorizontalPart_im](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean)
-/
@[path]
private lemma kwHorizontalPart_im_eq
  {z : ℂ} :
-- imply
  (kwHorizontalPart z).im = 0 := by
-- proof
  apply StatMech.FrontierA.kwHorizontalPart_im z

/--
[kwVerticalPart_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean)
-/
@[path]
private lemma kwVerticalPart_re_eq
  {z : ℂ} :
-- imply
  (kwVerticalPart z).re = 0 := by
-- proof
  apply StatMech.FrontierA.kwVerticalPart_re z

/--
[norm_kwHorizontalPart_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean)
-/
@[path]
private lemma norm_kwHorizontalPart_le_eq
  {z : ℂ} :
-- imply
  ‖kwHorizontalPart z‖ ≤ ‖z‖ := by
-- proof
  apply StatMech.FrontierA.norm_kwHorizontalPart_le z

/--
[norm_kwVerticalPart_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean)
-/
@[path]
private lemma norm_kwVerticalPart_le_eq
  {z : ℂ} :
-- imply
  ‖kwVerticalPart z‖ ≤ ‖z‖ := by
-- proof
  apply StatMech.FrontierA.norm_kwVerticalPart_le z

/--
[kwStairBase_mem_segment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean)
-/
@[path]
private lemma kwStairBase_mem_segment_eq
  {a b : ℂ}
  {N : ℕ}
  {k : Fin (N + 2)} :
-- imply
  kwStairBase a b N k ∈ segment ℝ a b := by
-- proof
  apply StatMech.FrontierA.kwStairBase_mem_segment a b N k

/--
[kwStairBase_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean)
-/
@[path]
private lemma kwStairBase_zero_eq
  {a b : ℂ}
  {N : ℕ} :
-- imply
  kwStairBase a b N 0 = a := by
-- proof
  apply StatMech.FrontierA.kwStairBase_zero a b N

/--
[kwStairBase_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean)
-/
@[path]
private lemma kwStairBase_last_eq
  {a b : ℂ}
  {N : ℕ} :
-- imply
  kwStairBase a b N (Fin.last (N + 1)) = b := by
-- proof
  apply StatMech.FrontierA.kwStairBase_last a b N

/--
[kwStairBase_succ_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean)
-/
@[path]
private lemma kwStairBase_succ_sub_eq
  {a b : ℂ}
  {N : ℕ}
  {k : Fin (N + 1)} :
-- imply
  kwStairBase a b N k.succ - kwStairBase a b N k.castSucc = (N + 1 : ℝ)⁻¹ * (b - a) := by
-- proof
  apply StatMech.FrontierA.kwStairBase_succ_sub a b N k

/--
[kwStairCorner_sub_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean)
-/
@[path]
private lemma kwStairCorner_sub_base_eq
  {a b : ℂ}
  {N : ℕ}
  {k : Fin (N + 1)} :
-- imply
  kwStairCorner a b N k - kwStairBase a b N k.castSucc = (N + 1 : ℝ)⁻¹ * kwHorizontalPart (b - a) := by
-- proof
  apply StatMech.FrontierA.kwStairCorner_sub_base a b N k

/--
[kwStairBase_succ_sub_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean)
-/
@[path]
private lemma kwStairBase_succ_sub_corner_eq
  {a b : ℂ}
  {N : ℕ}
  {k : Fin (N + 1)} :
-- imply
  kwStairBase a b N k.succ - kwStairCorner a b N k = (N + 1 : ℝ)⁻¹ * kwVerticalPart (b - a) := by
-- proof
  apply StatMech.FrontierA.kwStairBase_succ_sub_corner a b N k

/--
[dist_kwStairCorner_base_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean)
-/
@[path]
private lemma dist_kwStairCorner_base_le_eq
  {a b : ℂ}
  {N : ℕ}
  {k : Fin (N + 1)} :
-- imply
  dist (kwStairCorner a b N k) (kwStairBase a b N k.castSucc) ≤ ‖b - a‖ / (N + 1 : ℝ) := by
-- proof
  apply StatMech.FrontierA.dist_kwStairCorner_base_le a b N k

/--
[KWFiniteSimplePolygon.kwStairCorner_mem_closedEdgeTube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean)
-/
@[path]
private lemma kwStairCorner_mem_closedEdgeTube_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {N : ℕ}
  {k : Fin (N + 1)}
-- given
  (r : ℝ≥0)
  (hmesh : ‖polygon.edgeVector i‖ / (N + 1 : ℝ) < r) :
-- imply
  kwStairCorner (polygon.vertex i) (polygon.vertex (i + 1)) N k ∈ polygon.closedEdgeTube r i := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.kwStairCorner_mem_closedEdgeTube polygon i N k r hmesh

/--
[KWFiniteSimplePolygon.exists_uniform_stair_mesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean)
-/
@[path]
private lemma exists_uniform_stair_mesh_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (r : ℝ≥0)
  (hr : 0 < r) :
-- imply
  ∃ N : ℕ, ∀ i : Fin n, ‖polygon.edgeVector i‖ / (N + 1 : ℝ) < r := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_uniform_stair_mesh polygon r hr

/--
[KWFiniteSimplePolygon.exists_uniform_stair_corners_in_tubes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean)
-/
@[path]
private lemma exists_uniform_stair_corners_in_tubes_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (r : ℝ≥0)
  (hr : 0 < r) :
-- imply
  ∃ N : ℕ, ∀ i : Fin n, ∀ k : Fin (N + 1), kwStairCorner (polygon.vertex i) (polygon.vertex (i + 1)) N k ∈ polygon.closedEdgeTube r i := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_uniform_stair_corners_in_tubes polygon r hr


-- created on 2026-10-23
