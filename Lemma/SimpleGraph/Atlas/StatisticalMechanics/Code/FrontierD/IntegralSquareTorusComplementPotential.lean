import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusComplementPotential.Part2
open StatMech StatMech.FrontierD StatMech.FrontierD.IntegralSquareTorusCycle


/--
[sub_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean)
-/
@[path]
private lemma sub_horizontal_eq
  {L : Nat}
  [Fact (2 < L)]
  {C D : IntegralSquareTorusCycle L}
  {p : ZMod L × ZMod L} :
-- imply
  (C.sub D).horizontal p = C.horizontal p - D.horizontal p := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.sub_horizontal C D p

/--
[sub_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean)
-/
@[path]
private lemma sub_vertical_eq
  {L : Nat}
  [Fact (2 < L)]
  {C D : IntegralSquareTorusCycle L}
  {p : ZMod L × ZMod L} :
-- imply
  (C.sub D).vertical p = C.vertical p - D.vertical p := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.sub_vertical C D p

/--
[sub_xFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean)
-/
@[path]
private lemma sub_xFlux_eq
  {L : Nat}
  [Fact (2 < L)]
  {C D : IntegralSquareTorusCycle L}
  {x : ZMod L} :
-- imply
  (C.sub D).xFlux x = C.xFlux x - D.xFlux x := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.sub_xFlux C D x

/--
[sub_yFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean)
-/
@[path]
private lemma sub_yFlux_eq
  {L : Nat}
  [Fact (2 < L)]
  {C D : IntegralSquareTorusCycle L}
  {y : ZMod L} :
-- imply
  (C.sub D).yFlux y = C.yFlux y - D.yFlux y := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.sub_yFlux C D y

/--
[zeroFluxHorizontal_eq_horizontal_of_xFlux_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean)
-/
@[path]
private lemma zeroFluxHorizontal_eq_horizontal_of_xFlux_eq_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : ZMod L × ZMod L}
-- given
  (hC : C.xFlux (-1) = 0) :
-- imply
  C.zeroFluxHorizontal p = C.horizontal p := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.zeroFluxHorizontal_eq_horizontal_of_xFlux_eq_zero C hC p

/--
[zeroFluxVertical_eq_vertical_of_yFlux_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean)
-/
@[path]
private lemma zeroFluxVertical_eq_vertical_of_yFlux_eq_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : ZMod L × ZMod L}
-- given
  (hC : C.yFlux (-1) = 0) :
-- imply
  C.zeroFluxVertical p = C.vertical p := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.zeroFluxVertical_eq_vertical_of_yFlux_eq_zero C hC p

/--
[streamPotential_west_sub_of_yFlux_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean)
-/
@[path]
private lemma streamPotential_west_sub_of_yFlux_eq_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : ZMod L × ZMod L}
-- given
  (hC : C.yFlux (-1) = 0) :
-- imply
  C.streamPotential (p.1 - 1, p.2) - C.streamPotential p = C.vertical p := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.streamPotential_west_sub_of_yFlux_eq_zero C hC p

/--
[streamPotential_north_sub_of_xFlux_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean)
-/
@[path]
private lemma streamPotential_north_sub_of_xFlux_eq_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {C : IntegralSquareTorusCycle L}
  {p : ZMod L × ZMod L}
-- given
  (hC : C.xFlux (-1) = 0) :
-- imply
  C.streamPotential p - C.streamPotential (p.1, p.2 - 1) = C.horizontal p := by
-- proof
  apply StatMech.FrontierD.IntegralSquareTorusCycle.streamPotential_north_sub_of_xFlux_eq_zero C hC p

/--
[integralSquareTorusCycleListInteraction_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean)
-/
@[path]
private lemma integralSquareTorusCycleListInteraction_sub_eq
  {L : Nat}
  [Fact (8 < L)]
  {C D : IntegralSquareTorusCycle L}
  {l : List (ons_Dart L)} :
-- imply
  integralSquareTorusCycleListInteraction (C.sub D) l = integralSquareTorusCycleListInteraction C l - integralSquareTorusCycleListInteraction D l := by
-- proof
  apply StatMech.FrontierD.integralSquareTorusCycleListInteraction_sub C D l

/--
[integralSquareTorusCycleListInteraction_ofDartList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean)
-/
@[path]
private lemma integralSquareTorusCycleListInteraction_ofDartList_eq
  {L : Nat}
  [Fact (8 < L)]
  {a : List (ons_Dart L)}
  {l : List (ons_Dart L)}
-- given
  (ha : DartListBalanced a) :
-- imply
  integralSquareTorusCycleListInteraction (ofDartList a ha) l = fkRectRefinedRawInteraction a l := by
-- proof
  apply StatMech.FrontierD.integralSquareTorusCycleListInteraction_ofDartList a ha l

/--
[fkRectRefinedRawInteraction_singleton_eq_potentialIncrement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_singleton_eq_potentialIncrement_eq
  {L : Nat}
  [Fact (8 < L)]
  {C : IntegralSquareTorusCycle L}
  {d : ons_Dart L}
-- given
  (hx : C.xFlux (-1) = 0)
  (hy : C.yFlux (-1) = 0) :
-- imply
  (∑ p : ZMod L × ZMod L, (C.horizontal p * (([d].map (fun e => dartVertical e (p.1, p.2 - 1))).sum) - C.vertical p * (([d].map (fun e => dartHorizontal e (p.1 - 1, p.2))).sum))) = integralSquareTorusPotentialIncrement C d := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_singleton_eq_potentialIncrement C hx hy d

/--
[integralSquareTorusCycleListInteraction_eq_streamPotential_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean)
-/
@[path]
private lemma integralSquareTorusCycleListInteraction_eq_streamPotential_sub_eq
  {L : Nat}
  [Fact (8 < L)]
  {C : IntegralSquareTorusCycle L}
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (hx : C.xFlux (-1) = 0)
  (hy : C.yFlux (-1) = 0)
  (hl : FKRectIntegralSquareDartPath p q l) :
-- imply
  integralSquareTorusCycleListInteraction C (l.map (fkRectIntegralSquareDartMod L)) = C.streamPotential (fkRectIntegralSquarePointMod L q) - C.streamPotential (fkRectIntegralSquarePointMod L p) := by
-- proof
  apply StatMech.FrontierD.integralSquareTorusCycleListInteraction_eq_streamPotential_sub C hx hy hl

/--
[fkRectRefinedRawInteraction_sub_eq_of_equalFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_sub_eq_of_equalFlux_eq
  {L : Nat}
  [Fact (8 < L)]
  {a b : List (ons_Dart L)}
  {p q : Int × Int}
  {l k : List FKRectIntegralSquareDart}
-- given
  (ha : DartListBalanced a)
  (hb : DartListBalanced b)
  (hx : (ofDartList a ha).xFlux (-1) = (ofDartList b hb).xFlux (-1))
  (hy : (ofDartList a ha).yFlux (-1) = (ofDartList b hb).yFlux (-1))
  (hl : FKRectIntegralSquareDartPath p q l)
  (hk : FKRectIntegralSquareDartPath p q k) :
-- imply
  fkRectRefinedRawInteraction a (l.map (fkRectIntegralSquareDartMod L)) - fkRectRefinedRawInteraction b (l.map (fkRectIntegralSquareDartMod L)) = fkRectRefinedRawInteraction a (k.map (fkRectIntegralSquareDartMod L)) - fkRectRefinedRawInteraction b (k.map (fkRectIntegralSquareDartMod L)) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_sub_eq_of_equalFlux a b ha hb hx hy hl hk

/--
[fkRectRefinedRawInteraction_eq_streamPotential_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegralSquareTorusComplementPotential.lean)
-/
@[path]
private lemma fkRectRefinedRawInteraction_eq_streamPotential_sub_eq
  {L : Nat}
  [Fact (8 < L)]
  {a : List (ons_Dart L)}
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
-- given
  (ha : DartListBalanced a)
  (hx : (ofDartList a ha).xFlux (-1) = 0)
  (hy : (ofDartList a ha).yFlux (-1) = 0)
  (hl : FKRectIntegralSquareDartPath p q l) :
-- imply
  fkRectRefinedRawInteraction a (l.map (fkRectIntegralSquareDartMod L)) = (ofDartList a ha).streamPotential (fkRectIntegralSquarePointMod L q) - (ofDartList a ha).streamPotential (fkRectIntegralSquarePointMod L p) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedRawInteraction_eq_streamPotential_sub a ha hx hy hl


-- created on 2026-10-23
