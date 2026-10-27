import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionRectangularFekete
open Filter Topology StatMech StatMech.FrontierA


/--
[rectangularDobrushinArray_hasRectangularAreaBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionRectangularFekete.lean)
-/
@[path]
private lemma rectangularDobrushinArray_hasRectangularAreaBound_eq
  {J beta : Real} :
-- imply
  HasRectangularAreaBound (rectangularDobrushinArray J beta) := by
-- proof
  apply StatMech.FrontierA.rectangularDobrushinArray_hasRectangularAreaBound J beta

/--
[rectangularDobrushinArray_square_and_iterated_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionRectangularFekete.lean)
-/
@[path]
private lemma rectangularDobrushinArray_square_and_iterated_tendsto_eq
  {J beta : Real}
-- given
  (hJ : 0 <= J)
  (hbeta : 0 <= beta)
  (hsub : SeparatelySubadditive (rectangularDobrushinArray J beta)) :
-- imply
  Tendsto (fun n : Nat => rectangularSurfaceDensity (rectangularDobrushinArray J beta) n n) atTop (nhds (rectangularSurfaceRate (rectangularDobrushinArray J beta))) /\ Tendsto (fun k : Nat => (hsub.1 k).lim / (k : Real)) atTop (nhds (rectangularSurfaceRate (rectangularDobrushinArray J beta))) := by
-- proof
  apply StatMech.FrontierA.rectangularDobrushinArray_square_and_iterated_tendsto hJ hbeta hsub


-- created on 2026-10-23
