import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedRepeatedInteraction
open Finset StatMech StatMech.FrontierD


/--
[fkRectIntegralSquareDartTranslate_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedRepeatedInteraction.lean)
-/
@[path]
private lemma fkRectIntegralSquareDartTranslate_comp_eq
  {L : Nat}
  [Fact (8 < L)]
  {u v : Int × Int}
  {d : FKRectIntegralSquareDart} :
-- imply
  fkRectIntegralSquareDartTranslate u (fkRectIntegralSquareDartTranslate v d) = fkRectIntegralSquareDartTranslate (v.1 + u.1, v.2 + u.2) d := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralSquareDartTranslate_comp u v d

/--
[fkRectRefinedRawInteraction_integralTranslate_relative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedRepeatedInteraction.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_integralTranslate_relative_eq
  {L : Nat}
  [Fact (8 < L)]
  {a b : List FKRectIntegralSquareDart}
  {u v : Int × Int} :
-- imply
  fkRectRefinedRawInteraction ((a.map (fkRectIntegralSquareDartTranslate u)).map (fkRectIntegralSquareDartMod L)) ((b.map (fkRectIntegralSquareDartTranslate v)).map (fkRectIntegralSquareDartMod L)) = fkRectRefinedRawInteraction (a.map (fkRectIntegralSquareDartMod L)) ((b.map (fkRectIntegralSquareDartTranslate (v.1 - u.1, v.2 - u.2))).map (fkRectIntegralSquareDartMod L)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_integralTranslate_relative a b u v

/--
[fkRectRefinedRawInteraction_repeatTranslated_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedRepeatedInteraction.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeatTranslated_left_eq
  {L : Nat}
  [Fact (8 < L)]
  {l : List FKRectIntegralSquareDart}
  {u : Int × Int}
  {n : Nat}
  {b : List (StatMech.Onsager.ons_Dart L)} :
-- imply
  fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath l u n).map (fkRectIntegralSquareDartMod L)) b = ∑ k ∈ range n, fkRectRefinedRawInteraction ((l.map (fkRectIntegralSquareDartTranslate (fkRectNatScale k u))).map (fkRectIntegralSquareDartMod L)) b := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeatTranslated_left l u n b

/--
[fkRectRefinedRawInteraction_repeatTranslated_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedRepeatedInteraction.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeatTranslated_right_eq
  {L : Nat}
  [Fact (8 < L)]
  {a : List (StatMech.Onsager.ons_Dart L)}
  {l : List FKRectIntegralSquareDart}
  {u : Int × Int}
  {n : Nat} :
-- imply
  fkRectRefinedRawInteraction a ((fkRectRepeatTranslatedDartPath l u n).map (fkRectIntegralSquareDartMod L)) = ∑ k ∈ range n, fkRectRefinedRawInteraction a ((l.map (fkRectIntegralSquareDartTranslate (fkRectNatScale k u))).map (fkRectIntegralSquareDartMod L)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeatTranslated_right a l u n

/--
[fkRectRefinedRawInteraction_repeatTranslated_both](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedRepeatedInteraction.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_repeatTranslated_both_eq
  {L : Nat}
  [Fact (8 < L)]
  {a b : List FKRectIntegralSquareDart}
  {u v : Int × Int}
  {n m : Nat} :
-- imply
  fkRectRefinedRawInteraction ((fkRectRepeatTranslatedDartPath a u n).map (fkRectIntegralSquareDartMod L)) ((fkRectRepeatTranslatedDartPath b v m).map (fkRectIntegralSquareDartMod L)) = ∑ i ∈ range n, ∑ j ∈ range m, fkRectRefinedRawInteraction ((a.map (fkRectIntegralSquareDartTranslate (fkRectNatScale i u))).map (fkRectIntegralSquareDartMod L)) ((b.map (fkRectIntegralSquareDartTranslate (fkRectNatScale j v))).map (fkRectIntegralSquareDartMod L)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_repeatTranslated_both a b u v n m


-- created on 2026-10-23
