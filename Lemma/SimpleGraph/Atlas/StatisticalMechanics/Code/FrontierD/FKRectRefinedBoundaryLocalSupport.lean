import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundaryLocalSupport
open StatMech StatMech.FrontierD


/--
[fkRectRefinedBoundaryLocalInteraction_eq_zero_of_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryLocalSupport.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryLocalInteraction_eq_zero_of_open_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus}
  {c : Int × Int}
  {e : R.EdgeIndex}
-- given
  (hopen : pairing d.1 = !fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R d.1))
  (hc : FKRectRefinedEdgeCenterNormal (fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R d.1)) c) :
-- imply
  fkRectRefinedBoundaryLocalInteraction R pairing d c e = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryLocalInteraction_eq_zero_of_open R pairing d c e hopen hc

/--
[fkRectRefinedBoundaryLocalInteraction_eq_zero_of_endpointDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryLocalSupport.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryLocalInteraction_eq_zero_of_endpointDisjoint_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus}
  {c : Int × Int}
  {e : R.EdgeIndex}
-- given
  (hdisj : ∀ p, FKRectDartListUsesPoint ((fkRectRefinedLocalDarts (pairing d.1) c d.2).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p → ¬ FKRectDartListUsesPoint ((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p) :
-- imply
  fkRectRefinedBoundaryLocalInteraction R pairing d c e = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryLocalInteraction_eq_zero_of_endpointDisjoint R pairing d c e hdisj

/--
[fkRectRefinedBoundaryLocalInteraction_eq_zero_of_open_or_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryLocalSupport.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryLocalInteraction_eq_zero_of_open_or_disjoint_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus}
  {c : Int × Int}
  {e : R.EdgeIndex}
-- given
  (hc : FKRectRefinedEdgeCenterNormal (fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R d.1)) c)
  (hzero : pairing d.1 = !fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R d.1) ∨ ∀ p, FKRectDartListUsesPoint ((fkRectRefinedLocalDarts (pairing d.1) c d.2).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p → ¬ FKRectDartListUsesPoint ((fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) p) :
-- imply
  fkRectRefinedBoundaryLocalInteraction R pairing d c e = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryLocalInteraction_eq_zero_of_open_or_disjoint R pairing d c e hc hzero


-- created on 2026-10-23
