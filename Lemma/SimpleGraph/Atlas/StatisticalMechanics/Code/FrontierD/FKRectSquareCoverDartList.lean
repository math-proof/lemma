import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSquareCoverDartList
open StatMech StatMech.FrontierD


/--
[fkRectSquareCoverDartList_balanced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSquareCoverDartList.lean)
-/
@[path]
private lemma fkRectSquareCoverDartList_balanced_eq
  {R : FKRectTorus}
  {p u : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (h : FKRectIntegralSquareDartPath p (p.1 + u.1, p.2 + u.2) l) :
-- imply
  DartListBalanced (fkRectSquareCoverDartList R l u) := by
-- proof
  apply StatMech.FrontierD.fkRectSquareCoverDartList_balanced R h

/--
[fkRectSquareCoverDartList_xWrap_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSquareCoverDartList.lean)
-/
@[path]
private lemma fkRectSquareCoverDartList_xWrap_eq_eq
  {R : FKRectTorus}
  {p u : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (h : FKRectIntegralSquareDartPath p (p.1 + u.1, p.2 + u.2) l) :
-- imply
  ((fkRectSquareCoverDartList R l u).map ons_xWrapSign).sum = u.1 := by
-- proof
  apply StatMech.FrontierD.fkRectSquareCoverDartList_xWrap_eq R h

/--
[fkRectSquareCoverDartList_yWrap_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSquareCoverDartList.lean)
-/
@[path]
private lemma fkRectSquareCoverDartList_yWrap_eq_eq
  {R : FKRectTorus}
  {p u : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (h : FKRectIntegralSquareDartPath p (p.1 + u.1, p.2 + u.2) l) :
-- imply
  ((fkRectSquareCoverDartList R l u).map ons_yWrapSign).sum = u.2 := by
-- proof
  apply StatMech.FrontierD.fkRectSquareCoverDartList_yWrap_eq R h

/--
[fkRectSquareCoverDartList_interaction_ne_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSquareCoverDartList.lean)
-/
@[path]
private lemma fkRectSquareCoverDartList_interaction_ne_zero_iff_eq
  {R : FKRectTorus}
  [Fact (8 < fkRectSquareCoverSide R)]
  {p q u v : Int × Int}
  {a b : List FKRectIntegralSquareDart}
-- given
  (ha : FKRectIntegralSquareDartPath p (p.1 + u.1, p.2 + u.2) a)
  (hb : FKRectIntegralSquareDartPath q (q.1 + v.1, q.2 + v.2) b) :
-- imply
  fkRectRefinedRawInteraction (fkRectSquareCoverDartList R a u) (fkRectSquareCoverDartList R b v) ≠ 0 ↔ FKRectWindingIndependent u v := by
-- proof
  apply StatMech.FrontierD.fkRectSquareCoverDartList_interaction_ne_zero_iff R ha hb

/--
[fkRectSquareCoverDartList_interaction_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSquareCoverDartList.lean)
-/
@[path]
private lemma fkRectSquareCoverDartList_interaction_eq_zero_iff_eq
  {R : FKRectTorus}
  [Fact (8 < fkRectSquareCoverSide R)]
  {p q u v : Int × Int}
  {a b : List FKRectIntegralSquareDart}
-- given
  (ha : FKRectIntegralSquareDartPath p (p.1 + u.1, p.2 + u.2) a)
  (hb : FKRectIntegralSquareDartPath q (q.1 + v.1, q.2 + v.2) b) :
-- imply
  fkRectRefinedRawInteraction (fkRectSquareCoverDartList R a u) (fkRectSquareCoverDartList R b v) = 0 ↔ ¬ FKRectWindingIndependent u v := by
-- proof
  apply StatMech.FrontierD.fkRectSquareCoverDartList_interaction_eq_zero_iff R ha hb


-- created on 2026-10-23
