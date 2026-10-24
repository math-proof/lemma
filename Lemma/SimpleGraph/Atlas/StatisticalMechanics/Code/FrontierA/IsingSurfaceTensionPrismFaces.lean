import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionPrismFaces
open StatMech StatMech.FrontierA


/--
[sum_boundaryDegree_mul_eq_oddRectangularPrismFaceSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismFaces.lean)
-/
@[path]
private lemma sum_boundaryDegree_mul_eq_oddRectangularPrismFaceSum_eq
  {n : Nat}
-- given
  (f : RectangularPrismSite (2 * n + 1) (2 * n + 1) n -> Real) :
-- imply
  (∑ v, (rectangularPrismBoundaryDegree v : Real) * f v) = oddRectangularPrismFaceSum n f := by
-- proof
  apply StatMech.FrontierA.sum_boundaryDegree_mul_eq_oddRectangularPrismFaceSum n f

/--
[rectangularPrismPlusBoundaryInteraction_eq_faces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismFaces.lean)
-/
@[path]
private lemma rectangularPrismPlusBoundaryInteraction_eq_faces_eq
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n} :
-- imply
  rectangularPrismPlusBoundaryInteraction sigma = oddRectangularPrismFaceInteraction n sigma := by
-- proof
  apply StatMech.FrontierA.rectangularPrismPlusBoundaryInteraction_eq_faces n sigma

/--
[rectangularPrismDobrushinBoundaryInteraction_eq_faces](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionPrismFaces.lean)
-/
@[path]
private lemma rectangularPrismDobrushinBoundaryInteraction_eq_faces_eq
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n} :
-- imply
  (∑ v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n, oddRectangularPrismDobrushinSign n v.z * (rectangularPrismBoundaryDegree v : Real) * spin sigma v) = oddRectangularPrismDobrushinFaceInteraction n sigma := by
-- proof
  apply StatMech.FrontierA.rectangularPrismDobrushinBoundaryInteraction_eq_faces n sigma


-- created on 2026-10-23
