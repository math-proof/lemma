import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection.Part7
open StatMech StatMech.FrontierD


/--
[fkRectIntegralSquareDartMod_site](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma fkRectIntegralSquareDartMod_site_eq
  {L : Nat}
  {d : FKRectIntegralSquareDart} :
-- imply
  (fkRectIntegralSquareDartMod L d).1 = ((d.1.1 : ZMod L), (d.1.2 : ZMod L)) := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralSquareDartMod_site L d

/--
[fkRectIntegralSquareDartMod_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma fkRectIntegralSquareDartMod_end_eq
  {L : Nat}
  {d : FKRectIntegralSquareDart} :
-- imply
  ons_dirStep L (fkRectIntegralSquareDartMod L d).2 (fkRectIntegralSquareDartMod L d).1 = (((fkRectIntegralSquareDartEnd d).1 : ZMod L), ((fkRectIntegralSquareDartEnd d).2 : ZMod L)) := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralSquareDartMod_end L d

/--
[FKRectSquareAxisStep.exists_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma exists_direction_eq
  {p q : Int × Int}
-- given
  (h : FKRectSquareAxisStep p q) :
-- imply
  ∃ mu : Fin 4, fkRectIntegralSquareDartEnd (p, mu) = q := by
-- proof
  apply StatMech.FrontierD.FKRectSquareAxisStep.exists_direction h

/--
[FKRectSquareWalkLift.exists_integralDartPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma exists_integralDartPath_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x y}
  {p q : Int × Int}
-- given
  (h : FKRectSquareWalkLift R w p q) :
-- imply
  ∃ l : List FKRectIntegralSquareDart, FKRectIntegralSquareDartPath (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q) l ∧ l.length = w.darts.length := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.exists_integralDartPath R h

/--
[fkRectIntegralSquareDartEnd_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma fkRectIntegralSquareDartEnd_translate_eq
  {u : Int × Int}
  {d : FKRectIntegralSquareDart} :
-- imply
  fkRectIntegralSquareDartEnd (fkRectIntegralSquareDartTranslate u d) = ((fkRectIntegralSquareDartEnd d).1 + u.1, (fkRectIntegralSquareDartEnd d).2 + u.2) := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralSquareDartEnd_translate u d

/--
[FKRectIntegralSquareDartPath.translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma translate_eq
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
  {u : Int × Int}
-- given
  (h : FKRectIntegralSquareDartPath p q l) :
-- imply
  FKRectIntegralSquareDartPath (p.1 + u.1, p.2 + u.2) (q.1 + u.1, q.2 + u.2) (l.map (fkRectIntegralSquareDartTranslate u)) := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralSquareDartPath.translate h u

/--
[FKRectIntegralSquareDartPath.append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma append_eq
  {p q r : Int × Int}
  {l k : List FKRectIntegralSquareDart}
  {g : FKRectIntegralSquareDartPath q r k}
-- given
  (h : FKRectIntegralSquareDartPath p q l) :
-- imply
  FKRectIntegralSquareDartPath p r (l ++ k) := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralSquareDartPath.append h g

/--
[FKRectIntegralSquareDartPath.repeatTranslated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma repeatTranslated_eq
  {p u : Int × Int}
  {l : List FKRectIntegralSquareDart}
  {n : Nat}
-- given
  (h : FKRectIntegralSquareDartPath p (p.1 + u.1, p.2 + u.2) l) :
-- imply
  FKRectIntegralSquareDartPath p (p.1 + (n : Int) * u.1, p.2 + (n : Int) * u.2) (fkRectRepeatTranslatedDartPath l u n) := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralSquareDartPath.repeatTranslated h n

/--
[fkRectIntegralSquareDartMod_site_eq_pointMod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma fkRectIntegralSquareDartMod_site_eq_pointMod_eq
  {L : Nat}
  {d : FKRectIntegralSquareDart} :
-- imply
  (fkRectIntegralSquareDartMod L d).1 = fkRectIntegralSquarePointMod L d.1 := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralSquareDartMod_site_eq_pointMod L d

/--
[FKRectIntegralSquareDartPath.pointMass_telescope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma pointMass_telescope_eq
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
  {L : Nat}
  {z : ZMod L × ZMod L}
-- given
  (h : FKRectIntegralSquareDartPath p q l) :
-- imply
  ((l.map (fkRectIntegralSquareDartMod L)).map (fun d => IntegralSquareTorusCycle.pointMass d.1 z)).sum - ((l.map (fkRectIntegralSquareDartMod L)).map (fun d => IntegralSquareTorusCycle.pointMass (ons_dirStep L d.2 d.1) z)).sum = IntegralSquareTorusCycle.pointMass (fkRectIntegralSquarePointMod L p) z - IntegralSquareTorusCycle.pointMass (fkRectIntegralSquarePointMod L q) z := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralSquareDartPath.pointMass_telescope h L z

/--
[FKRectIntegralSquareDartPath.dartListBalanced_of_pointMod_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma dartListBalanced_of_pointMod_eq_eq
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
  {L : Nat}
-- given
  (h : FKRectIntegralSquareDartPath p q l)
  (hend : fkRectIntegralSquarePointMod L p = fkRectIntegralSquarePointMod L q) :
-- imply
  IntegralSquareTorusCycle.DartListBalanced (l.map (fkRectIntegralSquareDartMod L)) := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralSquareDartPath.dartListBalanced_of_pointMod_eq h L hend

/--
[fkRectIntegralSquareDart_displacement_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma fkRectIntegralSquareDart_displacement_x_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : FKRectIntegralSquareDart} :
-- imply
  (fkRectIntegralSquareDartEnd d).1 - d.1.1 = (((fkRectIntegralSquarePointMod L (fkRectIntegralSquareDartEnd d)).1.val : Nat) : Int) - (((fkRectIntegralSquarePointMod L d.1).1.val : Nat) : Int) + (L : Int) * ons_xWrapSign (fkRectIntegralSquareDartMod L d) := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralSquareDart_displacement_x d

/--
[fkRectIntegralSquareDart_displacement_y](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma fkRectIntegralSquareDart_displacement_y_eq
  {L : Nat}
  [Fact (2 < L)]
  {d : FKRectIntegralSquareDart} :
-- imply
  (fkRectIntegralSquareDartEnd d).2 - d.1.2 = (((fkRectIntegralSquarePointMod L (fkRectIntegralSquareDartEnd d)).2.val : Nat) : Int) - (((fkRectIntegralSquarePointMod L d.1).2.val : Nat) : Int) + (L : Int) * ons_yWrapSign (fkRectIntegralSquareDartMod L d) := by
-- proof
  apply StatMech.FrontierD.fkRectIntegralSquareDart_displacement_y d

/--
[FKRectIntegralSquareDartPath.displacement_x_eq_wrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma displacement_x_eq_wrap_eq
  {L : Nat}
  [Fact (2 < L)]
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (h : FKRectIntegralSquareDartPath p q l) :
-- imply
  q.1 - p.1 = (((fkRectIntegralSquarePointMod L q).1.val : Nat) : Int) - (((fkRectIntegralSquarePointMod L p).1.val : Nat) : Int) + (L : Int) * ((l.map (fkRectIntegralSquareDartMod L)).map ons_xWrapSign).sum := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralSquareDartPath.displacement_x_eq_wrap h

/--
[FKRectIntegralSquareDartPath.displacement_y_eq_wrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma displacement_y_eq_wrap_eq
  {L : Nat}
  [Fact (2 < L)]
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (h : FKRectIntegralSquareDartPath p q l) :
-- imply
  q.2 - p.2 = (((fkRectIntegralSquarePointMod L q).2.val : Nat) : Int) - (((fkRectIntegralSquarePointMod L p).2.val : Nat) : Int) + (L : Int) * ((l.map (fkRectIntegralSquareDartMod L)).map ons_yWrapSign).sum := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralSquareDartPath.displacement_y_eq_wrap h

/--
[fkRectSquareCoverSide_gt_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma fkRectSquareCoverSide_gt_two_eq
  {R : FKRectTorus} :
-- imply
  2 < fkRectSquareCoverSide R := by
-- proof
  apply StatMech.FrontierD.fkRectSquareCoverSide_gt_two R

/--
[FKRectIntegralSquareDartPath.exists_squareCoverCycleWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma exists_squareCoverCycleWitness_eq
  {R : FKRectTorus}
  {p u : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (h : FKRectIntegralSquareDartPath p (p.1 + u.1, p.2 + u.2) l) :
-- imply
  Nonempty (FKRectSquareCoverCycleWitness R u) := by
-- proof
  apply StatMech.FrontierD.FKRectIntegralSquareDartPath.exists_squareCoverCycleWitness R h

/--
[FKRectSquareWalkLift.exists_squareCoverCycleWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma exists_squareCoverCycleWitness_eq_2
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x : R.Vertex}
  {w : G.Walk x x}
  {p q : Int × Int}
-- given
  (h : FKRectSquareWalkLift R w p q) :
-- imply
  Nonempty (FKRectSquareCoverCycleWitness R (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p)) := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.exists_squareCoverCycleWitness R h

/--
[FKRectSquareCoverCycleWitness.not_independent_of_locallyDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma not_independent_of_locallyDisjoint_eq
  {R : FKRectTorus}
  {u v : Int × Int}
  {C : FKRectSquareCoverCycleWitness R u}
  {D : FKRectSquareCoverCycleWitness R v}
-- given
  (hdisj : C.cycle.LocallyDisjoint D.cycle) :
-- imply
  ¬ FKRectWindingIndependent u v := by
-- proof
  apply StatMech.FrontierD.FKRectSquareCoverCycleWitness.not_independent_of_locallyDisjoint C D hdisj

/--
[FKRectSquareWalkLift.not_windingIndependent_of_locallyDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean)
-/
@[path]
private lemma not_windingIndependent_of_locallyDisjoint_eq
  {R : FKRectTorus}
  {G H : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x x}
  {z : H.Walk y y}
  {p q a b : Int × Int}
  {C : FKRectSquareCoverCycleWitness R (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p)}
  {D : FKRectSquareCoverCycleWitness R (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a)}
-- given
  (hw : FKRectSquareWalkLift R w p q)
  (hz : FKRectSquareWalkLift R z a b)
  (hdisj : C.cycle.LocallyDisjoint D.cycle) :
-- imply
  ¬ FKRectWindingIndependent (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.not_windingIndependent_of_locallyDisjoint R hw hz C D hdisj


-- created on 2026-10-23
