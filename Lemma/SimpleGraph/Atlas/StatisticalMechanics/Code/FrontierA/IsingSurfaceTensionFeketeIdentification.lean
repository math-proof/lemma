import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFeketeIdentification
open Filter Set Topology StatMech StatMech.FrontierA


/--
[rectangularSurfaceRate_eq_iteratedFeketeLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFeketeIdentification.lean)
-/
@[path]
private lemma rectangularSurfaceRate_eq_iteratedFeketeLimit_eq
  {F : Nat -> Nat -> Real}
-- given
  (hF : forall m n, 0 <= F m n)
  (hsub : SeparatelySubadditive F) :
-- imply
  rectangularSurfaceRate F = (horizontalStripRate_subadditive hF hsub.1 hsub.2).lim := by
-- proof
  apply StatMech.FrontierA.rectangularSurfaceRate_eq_iteratedFeketeLimit hF hsub

/--
[iteratedRectangularSurfaceDensity_tendsto_rate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFeketeIdentification.lean)
-/
@[path]
private lemma iteratedRectangularSurfaceDensity_tendsto_rate_eq
  {F : Nat -> Nat -> Real}
-- given
  (hF : forall m n, 0 <= F m n)
  (hsub : SeparatelySubadditive F) :
-- imply
  Tendsto (fun k : Nat => (hsub.1 k).lim / (k : Real)) atTop (nhds (rectangularSurfaceRate F)) := by
-- proof
  apply StatMech.FrontierA.iteratedRectangularSurfaceDensity_tendsto_rate hF hsub

/--
[square_and_iterated_surfaceDensity_tendsto_rate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFeketeIdentification.lean)
-/
@[path]
private lemma square_and_iterated_surfaceDensity_tendsto_rate_eq
  {F : Nat -> Nat -> Real}
-- given
  (hF : forall m n, 0 <= F m n)
  (hsub : SeparatelySubadditive F)
  (harea : HasRectangularAreaBound F) :
-- imply
  Tendsto (fun n : Nat => rectangularSurfaceDensity F n n) atTop (nhds (rectangularSurfaceRate F)) /\ Tendsto (fun k : Nat => (hsub.1 k).lim / (k : Real)) atTop (nhds (rectangularSurfaceRate F)) := by
-- proof
  apply StatMech.FrontierA.square_and_iterated_surfaceDensity_tendsto_rate hF hsub harea


-- created on 2026-10-23
