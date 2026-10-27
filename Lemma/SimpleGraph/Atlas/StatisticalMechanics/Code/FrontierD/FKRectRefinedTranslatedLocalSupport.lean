import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedTranslatedLocalSupport
open StatMech StatMech.FrontierD


/--
[fkRectRefinedLocalDarts_add_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedTranslatedLocalSupport.lean)
-/
@[path]
private lemma fkRectRefinedLocalDarts_add_center_eq
  {pairing : Bool}
  {c t : Int × Int}
  {side : FKMedialSide} :
-- imply
  fkRectRefinedLocalDarts pairing (c.1 + t.1, c.2 + t.2) side = (fkRectRefinedLocalDarts pairing c side).map (fkRectIntegralSquareDartTranslate t) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedLocalDarts_add_center pairing c t side

/--
[fkRectRefinedPrimalCenterlineDarts_add_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedTranslatedLocalSupport.lean)
-/
@[path]
private lemma fkRectRefinedPrimalCenterlineDarts_add_center_eq
  {pairing : Bool}
  {c t : Int × Int} :
-- imply
  fkRectRefinedPrimalCenterlineDarts pairing (c.1 + t.1, c.2 + t.2) = (fkRectRefinedPrimalCenterlineDarts pairing c).map (fkRectIntegralSquareDartTranslate t) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedPrimalCenterlineDarts_add_center pairing c t

/--
[fkRectRefinedLocalDarts_west_interaction_add_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedTranslatedLocalSupport.lean)
-/
@[path]
private lemma fkRectRefinedLocalDarts_west_interaction_add_center_eq
  {R : FKRectTorus}
  {pairing : Bool}
  {c t : Int × Int} :
-- imply
  fkRectRefinedRawInteraction ((fkRectRefinedLocalDarts pairing (c.1 + t.1, c.2 + t.2) .west).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) ((fkRectRefinedPrimalCenterlineDarts pairing (c.1 + t.1, c.2 + t.2)).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedLocalDarts_west_interaction_add_center R pairing c t

/--
[fkRectRefinedLocalDarts_east_interaction_add_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedTranslatedLocalSupport.lean)
-/
@[path]
private lemma fkRectRefinedLocalDarts_east_interaction_add_center_eq
  {R : FKRectTorus}
  {pairing : Bool}
  {c t : Int × Int} :
-- imply
  fkRectRefinedRawInteraction ((fkRectRefinedLocalDarts pairing (c.1 + t.1, c.2 + t.2) .east).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) ((fkRectRefinedPrimalCenterlineDarts pairing (c.1 + t.1, c.2 + t.2)).map (fkRectIntegralSquareDartMod (fkRectSquareCoverSide (fkRectRefinedCoverTorus R)))) = -1 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedLocalDarts_east_interaction_add_center R pairing c t


-- created on 2026-10-23
