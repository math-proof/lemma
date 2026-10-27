import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOrbitInteraction.Part2
open Equiv Finset StatMech StatMech.FrontierD


/--
[permOrbitSignedVisitTrace_eq_sum_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOrbitInteraction.lean)
-/
@[path]
private lemma permOrbitSignedVisitTrace_eq_sum_range_eq
  [Fintype alpha]
  [DecidableEq alpha]
  {sigma : Perm alpha}
  {d a b : alpha}
  {n : Nat} :
-- imply
  permOrbitSignedVisitTrace sigma d a b n = Finset.sum (range n) fun i => ((if (sigma ^ i) d = a then 1 else 0) : Int) - (if (sigma ^ i) d = b then 1 else 0) := by
-- proof
  apply StatMech.FrontierD.permOrbitSignedVisitTrace_eq_sum_range sigma d a b n

/--
[permOrbitSignedVisitTrace_orderOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOrbitInteraction.lean)
-/
@[path]
private lemma permOrbitSignedVisitTrace_orderOf_eq
  [Fintype alpha]
  [DecidableEq alpha]
  {sigma : Perm alpha}
  {d a b : alpha} :
-- imply
  permOrbitSignedVisitTrace sigma d a b (orderOf sigma) = (permOrbitVisitCount sigma d a : Int) - permOrbitVisitCount sigma d b := by
-- proof
  apply StatMech.FrontierD.permOrbitSignedVisitTrace_orderOf sigma d a b

/--
[fkRectRefinedRawInteraction_boundaryDarts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOrbitInteraction.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_boundaryDarts_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus}
  {c : Int × Int}
  {e : R.EdgeIndex}
  {n : Nat} :
-- imply
  fkRectRefinedRawInteraction ((fkRectRefinedBoundaryDarts pairing d c n).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) ((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) = fkRectRefinedBoundaryInteractionTrace R pairing e d c n := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_boundaryDarts R pairing d c e n

/--
[fkRectRefinedBoundaryInteractionTrace_eq_signedVisits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOrbitInteraction.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryInteractionTrace_eq_signedVisits_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {e : R.EdgeIndex}
  {a b d : FKMedialDart R.medialTorus}
  {c : Int × Int}
  {n : Nat}
-- given
  (hlocal : forall (d' : FKMedialDart R.medialTorus) (c' : Int × Int), fkRectRefinedBoundaryLocalInteraction R pairing d' c' e = (if d' = a then 1 else 0) - (if d' = b then 1 else 0)) :
-- imply
  fkRectRefinedBoundaryInteractionTrace R pairing e d c n = permOrbitSignedVisitTrace (fkMedialBoundaryStep pairing) d a b n := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryInteractionTrace_eq_signedVisits R pairing e a b d c n hlocal

/--
[fkRectRefinedBoundaryInteractionTrace_eq_signedVisits_of_hasLocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOrbitInteraction.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryInteractionTrace_eq_signedVisits_of_hasLocal_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {e : R.EdgeIndex}
  {a b d : FKMedialDart R.medialTorus}
  {c : Int × Int}
  {n : Nat}
-- given
  (hlocal : FKRectRefinedBoundaryHasLocalVisitInteraction R pairing e a b d c n) :
-- imply
  fkRectRefinedBoundaryInteractionTrace R pairing e d c n = permOrbitSignedVisitTrace (fkMedialBoundaryStep pairing) d a b n := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryInteractionTrace_eq_signedVisits_of_hasLocal R pairing e a b d c n hlocal

/--
[fkRectRefinedRawInteraction_boundaryOrbit_eq_visitCount_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOrbitInteraction.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_boundaryOrbit_eq_visitCount_sub_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {e : R.EdgeIndex}
  {a b d : FKMedialDart R.medialTorus}
  {c : Int × Int}
-- given
  (hlocal : forall (d' : FKMedialDart R.medialTorus) (c' : Int × Int), fkRectRefinedBoundaryLocalInteraction R pairing d' c' e = (if d' = a then 1 else 0) - (if d' = b then 1 else 0)) :
-- imply
  fkRectRefinedRawInteraction ((fkRectRefinedBoundaryDarts pairing d c (orderOf (fkMedialBoundaryStep pairing))).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) ((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) = (fkMedialBoundaryOrbitVisitCount pairing d a : Int) - fkMedialBoundaryOrbitVisitCount pairing d b := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_boundaryOrbit_eq_visitCount_sub R pairing e a b d c hlocal

/--
[fkRectRefinedRawInteraction_boundaryOrbit_eq_visitCount_sub_of_hasLocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOrbitInteraction.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_boundaryOrbit_eq_visitCount_sub_of_hasLocal_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {e : R.EdgeIndex}
  {a b d : FKMedialDart R.medialTorus}
  {c : Int × Int}
-- given
  (hlocal : FKRectRefinedBoundaryHasLocalVisitInteraction R pairing e a b d c (orderOf (fkMedialBoundaryStep pairing))) :
-- imply
  fkRectRefinedRawInteraction ((fkRectRefinedBoundaryDarts pairing d c (orderOf (fkMedialBoundaryStep pairing))).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) ((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) = (fkMedialBoundaryOrbitVisitCount pairing d a : Int) - fkMedialBoundaryOrbitVisitCount pairing d b := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_boundaryOrbit_eq_visitCount_sub_of_hasLocal R pairing e a b d c hlocal


-- created on 2026-10-23
