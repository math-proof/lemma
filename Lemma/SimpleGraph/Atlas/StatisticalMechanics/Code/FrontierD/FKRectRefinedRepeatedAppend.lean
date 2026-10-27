import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedRepeatedAppend
open Finset StatMech StatMech.FrontierD


/--
[fkRectRefinedRawInteraction_repeatTranslated_append_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedRepeatedAppend.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeatTranslated_append_right_eq
  {L : Nat}
  [Fact (8 < L)]
  {x : List (ons_Dart L)}
  {a b : List FKRectIntegralSquareDart}
  {u : Int × Int}
  {n : Nat} :
-- imply
  fkRectRefinedRawInteraction x ((fkRectRepeatTranslatedDartPath (a ++ b) u n).map (fkRectIntegralSquareDartMod L)) = fkRectRefinedRawInteraction x ((fkRectRepeatTranslatedDartPath a u n).map (fkRectIntegralSquareDartMod L)) + fkRectRefinedRawInteraction x ((fkRectRepeatTranslatedDartPath b u n).map (fkRectIntegralSquareDartMod L)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeatTranslated_append_right x a b u n

/--
[fkRectRefinedRawInteraction_repeatTranslated_append_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedRepeatedAppend.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeatTranslated_append_left_eq
  {L : Nat}
  [Fact (8 < L)]
  {a b : List FKRectIntegralSquareDart}
  {u : Int × Int}
  {n : Nat}
  {x : List (ons_Dart L)} :
-- imply
  fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath (a ++ b) u n).map (fkRectIntegralSquareDartMod L)) x = fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath a u n).map (fkRectIntegralSquareDartMod L)) x + fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath b u n).map (fkRectIntegralSquareDartMod L)) x := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeatTranslated_append_left a b u n x


-- created on 2026-10-23
