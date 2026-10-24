import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore
open Finset StatMech StatMech.FrontierD


/--
[fkRectRefinedCoverSide_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean)
-/
@[path]
private lemma fkRectRefinedCoverSide_eq_eq
  {R : FKRectTorus} :
-- imply
  fkRectSquareCoverSide (fkRectRefinedCoverTorus R) = 4 * fkRectSquareCoverSide R := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedCoverSide_eq R

/--
[fkRectSquareCoverSide_gt_eight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean)
-/
@[path]
private lemma fkRectSquareCoverSide_gt_eight_eq
  {R : FKRectTorus} :
-- imply
  8 < fkRectSquareCoverSide R := by
-- proof
  apply StatMech.FrontierD.fkRectSquareCoverSide_gt_eight R

/--
[FKRectSquareCoverCycleWitness.windingIndependent_of_intersection_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean)
-/
@[path]
private lemma windingIndependent_of_intersection_ne_zero_eq
  {R : FKRectTorus}
  {u v : Int × Int}
  {C : FKRectSquareCoverCycleWitness R u}
  {D : FKRectSquareCoverCycleWitness R v}
-- given
  (hne : C.cycle.intersection D.cycle ≠ 0) :
-- imply
  FKRectWindingIndependent u v := by
-- proof
  apply StatMech.FrontierD.FKRectSquareCoverCycleWitness.windingIndependent_of_intersection_ne_zero C D hne

/--
[fkRectWindingIndependent_four_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean)
-/
@[path]
private lemma fkRectWindingIndependent_four_iff_eq
  {u v : Int × Int} :
-- imply
  FKRectWindingIndependent (4 * u.1, 4 * u.2) (4 * v.1, 4 * v.2) <-> FKRectWindingIndependent u v := by
-- proof
  apply StatMech.FrontierD.fkRectWindingIndependent_four_iff u v

/--
[fkRectWindingIndependent_four_squareDeck_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean)
-/
@[path]
private lemma fkRectWindingIndependent_four_squareDeck_iff_eq
  {R : FKRectTorus}
  {u v : Int × Int} :
-- imply
  FKRectWindingIndependent (4 * (fkRectSquareDeckTranslation R u).1, 4 * (fkRectSquareDeckTranslation R u).2) (4 * (fkRectSquareDeckTranslation R v).1, 4 * (fkRectSquareDeckTranslation R v).2) <-> FKRectWindingIndependent u v := by
-- proof
  apply StatMech.FrontierD.fkRectWindingIndependent_four_squareDeck_iff R u v

/--
[not_windingIndependent_trans_of_middle_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean)
-/
@[path]
private lemma not_windingIndependent_trans_of_middle_ne_zero_eq
  {u b v : Int × Int}
-- given
  (hb : b ≠ (0, 0))
  (hub : ¬ FKRectWindingIndependent u b)
  (hbv : ¬ FKRectWindingIndependent b v) :
-- imply
  ¬ FKRectWindingIndependent u v := by
-- proof
  apply StatMech.FrontierD.not_windingIndependent_trans_of_middle_ne_zero u b v hb hub hbv

/--
[fkRectRefinedRawInteraction_append_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_append_left_eq
  {L : Nat}
  [Fact (8 < L)]
  {a b c : List (ons_Dart L)} :
-- imply
  fkRectRefinedRawInteraction (a ++ b) c = fkRectRefinedRawInteraction a c + fkRectRefinedRawInteraction b c := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_append_left a b c

/--
[fkRectRefinedRawInteraction_append_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_append_right_eq
  {L : Nat}
  [Fact (8 < L)]
  {a b c : List (ons_Dart L)} :
-- imply
  fkRectRefinedRawInteraction a (b ++ c) = fkRectRefinedRawInteraction a b + fkRectRefinedRawInteraction a c := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_append_right a b c

/--
[fkRectRefinedRawInteraction_eq_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_eq_intersection_eq
  {L : Nat}
  [Fact (8 < L)]
  {a b : List (ons_Dart L)}
-- given
  (ha : DartListBalanced a)
  (hb : DartListBalanced b) :
-- imply
  fkRectRefinedRawInteraction a b = (ofDartList a ha).intersection (ofDartList b hb) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_eq_intersection a b ha hb

/--
[fkRectRefinedRawInteraction_eq_wrap_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_eq_wrap_det_eq
  {L : Nat}
  [Fact (8 < L)]
  {a b : List (ons_Dart L)}
-- given
  (ha : DartListBalanced a)
  (hb : DartListBalanced b) :
-- imply
  fkRectRefinedRawInteraction a b = (a.map ons_xWrapSign).sum * (b.map ons_yWrapSign).sum - (a.map ons_yWrapSign).sum * (b.map ons_xWrapSign).sum := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_eq_wrap_det a b ha hb

/--
[fkRectRefinedRawInteraction_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_translate_eq
  {L : Nat}
  [Fact (8 < L)]
  {u : ZMod L × ZMod L}
  {a b : List (ons_Dart L)} :
-- imply
  fkRectRefinedRawInteraction (a.map (fkRectRefinedDartTranslateMod u)) (b.map (fkRectRefinedDartTranslateMod u)) = fkRectRefinedRawInteraction a b := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_translate u a b

/--
[fkRectIntegralSquareDartMod_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean)
-/
@[path]
private lemma fkRectIntegralSquareDartMod_translate_eq
  {L : Nat}
  [Fact (8 < L)]
  {u : Int × Int}
  {d : FKRectIntegralSquareDart} :
-- imply
  fkRectIntegralSquareDartMod L (fkRectIntegralSquareDartTranslate u d) = fkRectRefinedDartTranslateMod ((u.1 : ZMod L), (u.2 : ZMod L)) (fkRectIntegralSquareDartMod L d) := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralSquareDartMod_translate u d

/--
[fkRectRefinedRawInteraction_integralTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_integralTranslate_eq
  {L : Nat}
  [Fact (8 < L)]
  {u : Int × Int}
  {a b : List FKRectIntegralSquareDart} :
-- imply
  fkRectRefinedRawInteraction ((a.map (fkRectIntegralSquareDartTranslate u)).map (fkRectIntegralSquareDartMod L)) ((b.map (fkRectIntegralSquareDartTranslate u)).map (fkRectIntegralSquareDartMod L)) = fkRectRefinedRawInteraction (a.map (fkRectIntegralSquareDartMod L)) (b.map (fkRectIntegralSquareDartMod L)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_integralTranslate u a b


-- created on 2026-10-23
