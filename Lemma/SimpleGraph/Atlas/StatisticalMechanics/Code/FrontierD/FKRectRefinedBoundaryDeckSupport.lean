import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundaryDeckSupport
open StatMech StatMech.FrontierD


/--
[fkRectRefinedBoundaryPrimalLift_liftedVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryDeckSupport.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryPrimalLift_liftedVertex_eq
  {R : FKRectTorus}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectLiftedVertex R (fkRectRefinedBoundaryPrimalLift R d) = fkRectMedialDartPrimalLabel R d := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryPrimalLift_liftedVertex R d

/--
[fkRectRefinedBoundaryPrimalPotential_exists_deck](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryDeckSupport.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryPrimalPotential_exists_deck_eq
  {R : FKRectTorus}
  {d : FKMedialDart R.medialTorus} :
-- imply
  ∃ u : Int × Int, fkRectRefinedBoundaryPrimalPotential R d = (4 * (fkRectSquareDeckTranslation R u).1, 4 * (fkRectSquareDeckTranslation R u).2) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryPrimalPotential_exists_deck R d

/--
[fkRectRefinedBoundaryCenterAfter_exists_deck](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryDeckSupport.lean)
-/
@[path]
private lemma fkRectRefinedBoundaryCenterAfter_exists_deck_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {d : FKMedialDart R.medialTorus}
  {n : Nat} :
-- imply
  ∃ u : Int × Int, fkRectRefinedBoundaryCenterAfter pairing d (fkRectRefinedBoundaryCanonicalCenter R d) n = ((fkRectRefinedBoundaryCanonicalCenter R ((fkMedialBoundaryStep pairing)^[n] d)).1 + 4 * (fkRectSquareDeckTranslation R u).1, (fkRectRefinedBoundaryCanonicalCenter R ((fkMedialBoundaryStep pairing)^[n] d)).2 + 4 * (fkRectSquareDeckTranslation R u).2) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedBoundaryCenterAfter_exists_deck R pairing d n


-- created on 2026-10-23
