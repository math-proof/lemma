import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
open StatMech StatMech.Exact3D


/--
[surfaceTension_cubeFace_axis_le_of_convex_flip23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/SurfaceTensionConvexity.lean)
-/
@[path]
private lemma surfaceTension_cubeFace_axis_le_of_convex_flip23_eq
  {T : SurfaceVec3 → ℝ}
  {n a b : ℝ}
-- given
  (hconv : ConvexOn ℝ Set.univ T)
  (hflip : ∀ x y z : ℝ, T (surfaceVec3 x (-y) (-z)) = T (surfaceVec3 x y z)) :
-- imply
  T (surfaceVec3 n 0 0) ≤ T (surfaceVec3 n a b) := by
-- proof
  apply StatMech.Exact3D.surfaceTension_cubeFace_axis_le_of_convex_flip23 hconv hflip n a b

/--
[surfaceTension_cubeFace_xAxisRate_le_of_convex_flip23_hom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/SurfaceTensionConvexity.lean)
-/
@[path]
private lemma surfaceTension_cubeFace_xAxisRate_le_of_convex_flip23_hom_eq
  {T : SurfaceVec3 → ℝ}
  {n a b : ℝ}
-- given
  (hconv : ConvexOn ℝ Set.univ T)
  (hflip : ∀ x y z : ℝ, T (surfaceVec3 x (-y) (-z)) = T (surfaceVec3 x y z))
  (hhom : ∀ t : ℝ, 0 ≤ t → T (surfaceVec3 t 0 0) = t * T surfaceXAxisUnit)
  (hn : 0 ≤ n) :
-- imply
  n * T surfaceXAxisUnit ≤ T (surfaceVec3 n a b) := by
-- proof
  apply StatMech.Exact3D.surfaceTension_cubeFace_xAxisRate_le_of_convex_flip23_hom hconv hflip hhom hn

/--
[surfaceTension_cubeBoundary_xAxisRate_le_of_convex_signedPerm_hom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/SurfaceTensionConvexity.lean)
-/
@[path]
private lemma surfaceTension_cubeBoundary_xAxisRate_le_of_convex_signedPerm_hom_eq
  {T : SurfaceVec3 → ℝ}
  {n x y z : ℝ}
-- given
  (hconv : ConvexOn ℝ Set.univ T)
  (hflip1 : ∀ x y z : ℝ, T (surfaceVec3 (-x) y z) = T (surfaceVec3 x y z))
  (hflip2 : ∀ x y z : ℝ, T (surfaceVec3 x (-y) z) = T (surfaceVec3 x y z))
  (hflip3 : ∀ x y z : ℝ, T (surfaceVec3 x y (-z)) = T (surfaceVec3 x y z))
  (hswap12 : ∀ x y z : ℝ, T (surfaceVec3 y x z) = T (surfaceVec3 x y z))
  (hswap13 : ∀ x y z : ℝ, T (surfaceVec3 z y x) = T (surfaceVec3 x y z))
  (hhom : ∀ t : ℝ, 0 ≤ t → T (surfaceVec3 t 0 0) = t * T surfaceXAxisUnit)
  (hn : 0 ≤ n)
  (hface : x = n ∨ x = -n ∨ y = n ∨ y = -n ∨ z = n ∨ z = -n) :
-- imply
  n * T surfaceXAxisUnit ≤ T (surfaceVec3 x y z) := by
-- proof
  apply StatMech.Exact3D.surfaceTension_cubeBoundary_xAxisRate_le_of_convex_signedPerm_hom hconv hflip1 hflip2 hflip3 hswap12 hswap13 hhom hn hface


-- created on 2026-10-23
