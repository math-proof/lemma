import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenWalkCarrier
open StatMech StatMech.FrontierD


/--
[FKRectSquareWalkLift.mapLe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOpenWalkCarrier.lean)
-/
@[path]
private lemma mapLe_eq
  {R : FKRectTorus}
  {G H : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x y}
  {p q : Int × Int}
-- given
  (hGH : G ≤ H)
  (h : FKRectSquareWalkLift R w p q) :
-- imply
  FKRectSquareWalkLift R (w.mapLe hGH) p q := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.mapLe R hGH h

/--
[exists_fkRectRefinedOpenWalkCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOpenWalkCarrier.lean)
-/
@[path]
private lemma exists_fkRectRefinedOpenWalkCarrier_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {x y : R.Vertex}
  {w : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk x y}
  {p : Int × Int}
-- given
  (hp : fkRectLiftedVertex R p = x) :
-- imply
  ∃ q : Int × Int, ∃ l : List FKRectIntegralSquareDart, fkRectLiftedVertex R q = y ∧ FKRectSquareWalkLift R w p q ∧ FKRectIntegralSquareDartPath (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)) (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q)) l ∧ FKRectRefinedOpenEdgeBlocks R F l := by
-- proof
  apply StatMech.FrontierD.exists_fkRectRefinedOpenWalkCarrier R F w p hp

/--
[FKRectRefinedOpenEdgeBlocks.repeated_boundary_interaction_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedOpenWalkCarrier.lean)
-/
@[path]
private lemma repeated_boundary_interaction_eq_zero_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {l : List FKRectIntegralSquareDart}
  {d : FKMedialDart R.medialTorus}
  {n : Nat}
  {w z : Int × Int}
-- given
  (hl : FKRectRefinedOpenEdgeBlocks R F l) :
-- imply
  let pairing := fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F) let c := fkRectRefinedBoundaryCanonicalCenter R d let L := fkRectSquareCoverSide (fkRectRefinedCoverTorus R) let U : Int × Int := (4 * (fkRectSquareDeckTranslation R w).1, 4 * (fkRectSquareDeckTranslation R w).2) let V : Int × Int := (4 * (fkRectSquareDeckTranslation R z).1, 4 * (fkRectSquareDeckTranslation R z).2) fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (fkRectRefinedBoundaryDarts pairing d c n) U L).map (fkRectIntegralSquareDartMod L)) ((fkRectRepeatTranslatedDartPath l V L).map (fkRectIntegralSquareDartMod L)) = 0 := by
-- proof
  apply StatMech.FrontierD.FKRectRefinedOpenEdgeBlocks.repeated_boundary_interaction_eq_zero R F hl d n w z


-- created on 2026-10-23
