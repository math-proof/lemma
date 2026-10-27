import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectDevelopedStep_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDevelopedWinding.lean)
-/
@[path]
private lemma fkRectDevelopedStep_swap_eq
  {R : FKRectTorus}
  {x y : R.Vertex} :
-- imply
  fkRectDevelopedStep R y x = -fkRectDevelopedStep R x y := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedStep_swap R x y

/--
[fkRectWalkDevelopedDisplacement_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDevelopedWinding.lean)
-/
@[path]
private lemma fkRectWalkDevelopedDisplacement_eq_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {p : G.Walk x y} :
-- imply
  fkRectWalkDevelopedDisplacement R p = (((y.1.val : Int) - x.1.val) + (R.width : Int) * (fkRectWalkWinding R p).1, ((y.2.val : Int) - x.2.val) + (R.height : Int) * (fkRectWalkWinding R p).2) := by
-- proof
  apply StatMech.FrontierD.fkRectWalkDevelopedDisplacement_eq R p

/--
[fkRectClosedWalkDevelopedDisplacement_eq_period_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDevelopedWinding.lean)
-/
@[path]
private lemma fkRectClosedWalkDevelopedDisplacement_eq_period_winding_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x : R.Vertex}
  {p : G.Walk x x} :
-- imply
  fkRectWalkDevelopedDisplacement R p = ((R.width : Int) * (fkRectWalkWinding R p).1, (R.height : Int) * (fkRectWalkWinding R p).2) := by
-- proof
  apply StatMech.FrontierD.fkRectClosedWalkDevelopedDisplacement_eq_period_winding R p

/--
[fkRectWindingIndependent_period_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDevelopedWinding.lean)
-/
@[path]
private lemma fkRectWindingIndependent_period_iff_eq
  {R : FKRectTorus}
  {u v : Int × Int} :
-- imply
  FKRectWindingIndependent ((R.width : Int) * u.1, (R.height : Int) * u.2) ((R.width : Int) * v.1, (R.height : Int) * v.2) <-> FKRectWindingIndependent u v := by
-- proof
  apply StatMech.FrontierD.fkRectWindingIndependent_period_iff R u v


-- created on 2026-10-23
