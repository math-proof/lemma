import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersectionCriterion
open StatMech StatMech.FrontierD


/--
[FKRectSquareCoverCycleWitness.windingIndependent_iff_intersection_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersectionCriterion.lean)
-/
@[path]
private lemma windingIndependent_iff_intersection_ne_zero_eq
  {R : FKRectTorus}
  {u v : Int × Int}
  {C : FKRectSquareCoverCycleWitness R u}
  {D : FKRectSquareCoverCycleWitness R v} :
-- imply
  FKRectWindingIndependent u v ↔ C.cycle.intersection D.cycle ≠ 0 := by
-- proof
  apply StatMech.FrontierD.FKRectSquareCoverCycleWitness.windingIndependent_iff_intersection_ne_zero C D

/--
[fkRectRefinedSquareCoverIntersection_ne_zero_iff_windingIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersectionCriterion.lean)
-/
@[path]
private lemma fkRectRefinedSquareCoverIntersection_ne_zero_iff_windingIndependent_eq
  {R : FKRectTorus}
  {u v : Int × Int}
  {C : FKRectSquareCoverCycleWitness R (4 * (fkRectSquareDeckTranslation R u).1, 4 * (fkRectSquareDeckTranslation R u).2)}
  {D : FKRectSquareCoverCycleWitness R (4 * (fkRectSquareDeckTranslation R v).1, 4 * (fkRectSquareDeckTranslation R v).2)} :
-- imply
  C.cycle.intersection D.cycle ≠ 0 ↔ FKRectWindingIndependent u v := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedSquareCoverIntersection_ne_zero_iff_windingIndependent R u v C D

/--
[fkRectFourSquareDeck_ne_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersectionCriterion.lean)
-/
@[path]
private lemma fkRectFourSquareDeck_ne_zero_iff_eq
  {R : FKRectTorus}
  {u : Int × Int} :
-- imply
  (4 * (fkRectSquareDeckTranslation R u).1, 4 * (fkRectSquareDeckTranslation R u).2) ≠ (0, 0) ↔ u ≠ (0, 0) := by
-- proof
  apply StatMech.FrontierD.fkRectFourSquareDeck_ne_zero_iff R u

/--
[fkRectRefinedRawInteraction_ne_zero_iff_windingIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersectionCriterion.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_ne_zero_iff_windingIndependent_eq
  {L : Nat}
  [Fact (8 < L)]
  {a b : List (ons_Dart L)}
-- given
  (ha : DartListBalanced a)
  (hb : DartListBalanced b) :
-- imply
  fkRectRefinedRawInteraction a b ≠ 0 ↔ FKRectWindingIndependent ((a.map ons_xWrapSign).sum, (a.map ons_yWrapSign).sum) ((b.map ons_xWrapSign).sum, (b.map ons_yWrapSign).sum) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_ne_zero_iff_windingIndependent a b ha hb

/--
[fkRectRefinedRawInteraction_eq_zero_iff_not_windingIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersectionCriterion.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_eq_zero_iff_not_windingIndependent_eq
  {L : Nat}
  [Fact (8 < L)]
  {a b : List (ons_Dart L)}
-- given
  (ha : DartListBalanced a)
  (hb : DartListBalanced b) :
-- imply
  fkRectRefinedRawInteraction a b = 0 ↔ ¬ FKRectWindingIndependent ((a.map ons_xWrapSign).sum, (a.map ons_yWrapSign).sum) ((b.map ons_xWrapSign).sum, (b.map ons_yWrapSign).sum) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_eq_zero_iff_not_windingIndependent a b ha hb


-- created on 2026-10-23
