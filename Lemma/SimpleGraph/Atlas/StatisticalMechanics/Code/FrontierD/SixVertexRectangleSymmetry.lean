import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry.Part3
open Finset StatMech StatMech.FrontierD


/--
[sixVertexRectangleReflectHorizontal_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleSymmetry.lean)
-/
@[path]
private lemma sixVertexRectangleReflectHorizontal_involutive_eq
  {N M : ℕ}
  {ω : SixVertexRectangleArrows N M} :
-- imply
  sixVertexRectangleReflectHorizontal (sixVertexRectangleReflectHorizontal ω) = ω := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleReflectHorizontal_involutive ω

/--
[sixVertexRectangleReflectVertical_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleSymmetry.lean)
-/
@[path]
private lemma sixVertexRectangleReflectVertical_involutive_eq
  {N M : ℕ}
  {ω : SixVertexRectangleArrows N M} :
-- imply
  sixVertexRectangleReflectVertical (sixVertexRectangleReflectVertical ω) = ω := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleReflectVertical_involutive ω

/--
[sixVertexRectangleReflectHorizontal_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleSymmetry.lean)
-/
@[path]
private lemma sixVertexRectangleReflectHorizontal_boundary_eq
  {N M : ℕ}
  {ω : SixVertexRectangleArrows N M} :
-- imply
  sixVertexRectangleBoundary (sixVertexRectangleReflectHorizontal ω) = sixVertexBoundaryReflectHorizontal (sixVertexRectangleBoundary ω) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleReflectHorizontal_boundary ω

/--
[sixVertexRectangleReflectVertical_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleSymmetry.lean)
-/
@[path]
private lemma sixVertexRectangleReflectVertical_boundary_eq
  {N M : ℕ}
  {ω : SixVertexRectangleArrows N M} :
-- imply
  sixVertexRectangleBoundary (sixVertexRectangleReflectVertical ω) = sixVertexBoundaryReflectVertical (sixVertexRectangleBoundary ω) := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleReflectVertical_boundary ω

/--
[sixVertexBoundaryReflectHorizontal_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleSymmetry.lean)
-/
@[path]
private lemma sixVertexBoundaryReflectHorizontal_involutive_eq
  {N M : ℕ}
  {ξ : SixVertexRectangleBoundary N M} :
-- imply
  sixVertexBoundaryReflectHorizontal (sixVertexBoundaryReflectHorizontal ξ) = ξ := by
-- proof
  apply StatMech.FrontierD.sixVertexBoundaryReflectHorizontal_involutive ξ

/--
[sixVertexBoundaryReflectVertical_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleSymmetry.lean)
-/
@[path]
private lemma sixVertexBoundaryReflectVertical_involutive_eq
  {N M : ℕ}
  {ξ : SixVertexRectangleBoundary N M} :
-- imply
  sixVertexBoundaryReflectVertical (sixVertexBoundaryReflectVertical ξ) = ξ := by
-- proof
  apply StatMech.FrontierD.sixVertexBoundaryReflectVertical_involutive ξ

/--
[sixVertexRectangleReflectHorizontal_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleSymmetry.lean)
-/
@[path]
private lemma sixVertexRectangleReflectHorizontal_weight_eq
  {N M : ℕ}
  {c : ℝ}
  {ω : SixVertexRectangleArrows N M} :
-- imply
  (sixVertexRectangleReflectHorizontal ω).weight c = ω.weight c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleReflectHorizontal_weight c ω

/--
[sixVertexRectangleReflectVertical_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleSymmetry.lean)
-/
@[path]
private lemma sixVertexRectangleReflectVertical_weight_eq
  {N M : ℕ}
  {c : ℝ}
  {ω : SixVertexRectangleArrows N M} :
-- imply
  (sixVertexRectangleReflectVertical ω).weight c = ω.weight c := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleReflectVertical_weight c ω

/--
[sixVertexRectangleBoundaryPartitionSum_reflectHorizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleSymmetry.lean)
-/
@[path]
private lemma sixVertexRectangleBoundaryPartitionSum_reflectHorizontal_eq
  {N M : ℕ}
  {c : ℝ}
  {ξ : SixVertexRectangleBoundary N M} :
-- imply
  sixVertexRectangleBoundaryPartitionSum N M c (sixVertexBoundaryReflectHorizontal ξ) = sixVertexRectangleBoundaryPartitionSum N M c ξ := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBoundaryPartitionSum_reflectHorizontal N M c ξ

/--
[sixVertexRectangleBoundaryPartitionSum_reflectVertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleSymmetry.lean)
-/
@[path]
private lemma sixVertexRectangleBoundaryPartitionSum_reflectVertical_eq
  {N M : ℕ}
  {c : ℝ}
  {ξ : SixVertexRectangleBoundary N M} :
-- imply
  sixVertexRectangleBoundaryPartitionSum N M c (sixVertexBoundaryReflectVertical ξ) = sixVertexRectangleBoundaryPartitionSum N M c ξ := by
-- proof
  apply StatMech.FrontierD.sixVertexRectangleBoundaryPartitionSum_reflectVertical N M c ξ


-- created on 2026-10-23
