import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedSupportInteraction.Part2
open Finset StatMech StatMech.FrontierD


/--
[fkRectRefinedRawInteraction_eq_zero_of_endpointDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedSupportInteraction.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_eq_zero_of_endpointDisjoint_eq
  {L : Nat}
  [Fact (8 < L)]
  {v w : List (StatMech.Onsager.ons_Dart L)}
-- given
  (hdisj : ∀ p, FKRectDartListUsesPoint v p → ¬ FKRectDartListUsesPoint w p) :
-- imply
  fkRectRefinedRawInteraction v w = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_eq_zero_of_endpointDisjoint v w hdisj

/--
[fkRectIntegralSquareDartMod_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedSupportInteraction.lean)
-/
@[path]
private lemma fkRectIntegralSquareDartMod_dir_eq
  {L : Nat}
  {d : FKRectIntegralSquareDart} :
-- imply
  (fkRectIntegralSquareDartMod L d).2 = d.2 := by
-- proof
  apply fkRectIntegralSquareDartMod_dir L d

/--
[fkRectRefinedPrimalEdgeCenter_normal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedSupportInteraction.lean)
-/
@[path]
private lemma fkRectRefinedPrimalEdgeCenter_normal_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  FKRectRefinedEdgeCenterNormal (fkRectClosedPairingAtEdge e) (fkRectRefinedPrimalEdgeCenter R e) := by
-- proof
  apply fkRectRefinedPrimalEdgeCenter_normal R e

/--
[FKRectRefinedEdgeCenterNormal.add_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedSupportInteraction.lean)
-/
@[path]
private lemma add_four_eq
  {horizontal : Bool}
  {c : Int × Int}
  {u v : Int}
-- given
  (hc : FKRectRefinedEdgeCenterNormal horizontal c) :
-- imply
  FKRectRefinedEdgeCenterNormal horizontal (c.1 + 4 * u, c.2 + 4 * v) := by
-- proof
  apply FKRectRefinedEdgeCenterNormal.add_four hc u v

/--
[fkRectRefinedBoundaryCanonicalCenter_normal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedSupportInteraction.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryCanonicalCenter_normal_eq
  {R : FKRectTorus}
  {d : FKMedialDart R.medialTorus} :
-- imply
  FKRectRefinedEdgeCenterNormal (fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R d.1)) (fkRectRefinedBoundaryCanonicalCenter R d) := by
-- proof
  apply fkRectRefinedBoundaryCanonicalCenter_normal R d

/--
[fkRectRefinedBoundaryCenterAfter_normal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedSupportInteraction.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryCenterAfter_normal_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus}
  {n : Nat} :
-- imply
  FKRectRefinedEdgeCenterNormal (fkRectClosedPairingAtEdge (fkRectTorusMedialEdgeEquiv R (((fkMedialBoundaryStep pairing)^[n] d).1))) (fkRectRefinedBoundaryCenterAfter pairing d (fkRectRefinedBoundaryCanonicalCenter R d) n) := by
-- proof
  apply fkRectRefinedBoundaryCenterAfter_normal R pairing d n

/--
[fkRectRefinedLocalDarts_open_interaction_of_normalCenters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedSupportInteraction.lean)
-/
@[path]
private lemma fkRectRefinedLocalDarts_open_interaction_of_normalCenters_eq
  {R : FKRectTorus}
  {closed targetHorizontal : Bool}
  {c z : Int × Int}
  {side : FKMedialSide}
-- given
  (hc : FKRectRefinedEdgeCenterNormal closed c)
  (hz : FKRectRefinedEdgeCenterNormal targetHorizontal z) :
-- imply
  fkRectRefinedRawInteraction ((fkRectRefinedLocalDarts (!closed) c side).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) ((fkRectRefinedPrimalCenterlineDarts targetHorizontal z).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) = 0 := by
-- proof
  apply fkRectRefinedLocalDarts_open_interaction_of_normalCenters R closed targetHorizontal c z side hc hz


-- created on 2026-10-23
