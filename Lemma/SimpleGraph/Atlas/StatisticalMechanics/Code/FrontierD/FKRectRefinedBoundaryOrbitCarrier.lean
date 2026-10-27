import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundaryOrbitCarrier
open StatMech StatMech.FrontierD


/--
[fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOrbitCarrier.lean)
-/
@[path]
private lemma fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  FKRectIntegralSquareDartPath (fkRectRefinedDartPoint (fkRectRefinedBoundaryCanonicalCenter R d) d.2) ((fkRectRefinedDartPoint (fkRectRefinedBoundaryCanonicalCenter R d) d.2).1 + (fkRectRefinedBoundaryOrbitTranslation (fkRectConfigurationToMedialPairing R omega) d (fkRectRefinedBoundaryCanonicalCenter R d)).1, (fkRectRefinedDartPoint (fkRectRefinedBoundaryCanonicalCenter R d) d.2).2 + (fkRectRefinedBoundaryOrbitTranslation (fkRectConfigurationToMedialPairing R omega) d (fkRectRefinedBoundaryCanonicalCenter R d)).2) (fkRectCanonicalRefinedBoundaryOrbitDarts R omega d) := by
-- proof
  apply StatMech.FrontierD.fkRectCanonicalRefinedBoundaryOrbitDarts_path_translation R omega d

/--
[fkRectRefinedBoundaryOrbitTranslation_ne_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOrbitCarrier.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryOrbitTranslation_ne_zero_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectRefinedBoundaryOrbitTranslation (fkRectConfigurationToMedialPairing R omega) d (fkRectRefinedBoundaryCanonicalCenter R d) ≠ (0, 0) ↔ fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d) ≠ (0, 0) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryOrbitTranslation_ne_zero_iff R omega d

/--
[fkRectCanonicalBoundaryOrbitCarrier_interaction_ne_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOrbitCarrier.lean)
-/
@[path]
private lemma fkRectCanonicalBoundaryOrbitCarrier_interaction_ne_zero_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus}
  {G : SimpleGraph R.Vertex}
  {x : R.Vertex}
  {w : G.Walk x x}
  {p q : Int × Int}
  {hw : FKRectSquareWalkLift R w p q}
  {C : FKRectRefinedWalkCarrier R hw} :
-- imply
  fkRectRefinedRawInteraction (fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega d) C.coverDarts ≠ 0 ↔ FKRectWindingIndependent (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d)) (fkRectWalkWinding R w) := by
-- proof
  apply StatMech.FrontierD.fkRectCanonicalBoundaryOrbitCarrier_interaction_ne_zero_iff R omega d C

/--
[fkRectCanonicalBoundaryOrbitCarrier_interaction_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryOrbitCarrier.lean)
-/
@[path]
private lemma fkRectCanonicalBoundaryOrbitCarrier_interaction_eq_zero_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus}
  {G : SimpleGraph R.Vertex}
  {x : R.Vertex}
  {w : G.Walk x x}
  {p q : Int × Int}
  {hw : FKRectSquareWalkLift R w p q}
  {C : FKRectRefinedWalkCarrier R hw} :
-- imply
  fkRectRefinedRawInteraction (fkRectCanonicalRefinedBoundaryOrbitCoverDarts R omega d) C.coverDarts = 0 ↔ ¬ FKRectWindingIndependent (fkRectWalkWinding R (fkRectMedialBoundaryPrimalOrbitWalk R omega d)) (fkRectWalkWinding R w) := by
-- proof
  apply StatMech.FrontierD.fkRectCanonicalBoundaryOrbitCarrier_interaction_eq_zero_iff R omega d C


-- created on 2026-10-23
