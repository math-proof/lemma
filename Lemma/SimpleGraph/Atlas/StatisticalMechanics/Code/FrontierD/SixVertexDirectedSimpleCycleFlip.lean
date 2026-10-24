import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexDirectedSimpleCycleFlip
open StatMech StatMech.FrontierD


/--
[SixVertexDirectedSimpleCycle.mask_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean)
-/
@[path]
private lemma mask_horizontal_eq
  {T : EvenTorus}
  {cycle : SixVertexDirectedSimpleCycle T}
  {base : T.Vertex} :
-- imply
  cycle.mask.horizontal base = true <-> exists i, (cycle.edge i).physical = (false, base) := by
-- proof
  apply StatMech.FrontierD.SixVertexDirectedSimpleCycle.mask_horizontal cycle base

/--
[SixVertexDirectedSimpleCycle.mask_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean)
-/
@[path]
private lemma mask_vertical_eq
  {T : EvenTorus}
  {cycle : SixVertexDirectedSimpleCycle T}
  {base : T.Vertex} :
-- imply
  cycle.mask.vertical base = true <-> exists i, (cycle.edge i).physical = (true, base) := by
-- proof
  apply StatMech.FrontierD.SixVertexDirectedSimpleCycle.mask_vertical cycle base

/--
[sixVertexDirectedTorusEdge_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean)
-/
@[path]
private lemma sixVertexDirectedTorusEdge_divergence_eq
  {T : EvenTorus}
  {edge : SixVertexDirectedTorusEdge T}
  {v : T.Vertex} :
-- imply
  edge.horizontalFlow (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) + edge.verticalFlow (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) - edge.horizontalFlow v - edge.verticalFlow v = (if edge.head = v then 1 else 0) - (if edge.tail = v then 1 else 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexDirectedTorusEdge_divergence edge v

/--
[SixVertexDirectedSimpleCycle.isCirculation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean)
-/
@[path]
private lemma isCirculation_eq
  {T : EvenTorus}
  {cycle : SixVertexDirectedSimpleCycle T} :
-- imply
  SixVertexTorusCirculation T cycle.horizontalFlow cycle.verticalFlow := by
-- proof
  apply StatMech.FrontierD.SixVertexDirectedSimpleCycle.isCirculation cycle

/--
[sixVertexIceRule_of_flowConservation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean)
-/
@[path]
private lemma sixVertexIceRule_of_flowConservation_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
-- given
  (hflow : SixVertexTorusCirculation T (fun v => (omega.horizontal v).toNat) (fun v => (omega.vertical v).toNat)) :
-- imply
  omega.IceRule := by
-- proof
  apply StatMech.FrontierD.sixVertexIceRule_of_flowConservation omega hflow

/--
[SixVertexDirectedSimpleCycle.flip_horizontal_toNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean)
-/
@[path]
private lemma flip_horizontal_toNat_eq
  {T : EvenTorus}
  {cycle : SixVertexDirectedSimpleCycle T}
  {omega : SixVertexArrows T}
  {base : T.Vertex}
-- given
  (hfollows : cycle.Follows omega) :
-- imply
  ((sixVertexTorusFlip cycle.mask omega).horizontal base).toNat = (omega.horizontal base).toNat - cycle.horizontalFlow base := by
-- proof
  apply StatMech.FrontierD.SixVertexDirectedSimpleCycle.flip_horizontal_toNat cycle omega hfollows base

/--
[SixVertexDirectedSimpleCycle.flip_vertical_toNat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean)
-/
@[path]
private lemma flip_vertical_toNat_eq
  {T : EvenTorus}
  {cycle : SixVertexDirectedSimpleCycle T}
  {omega : SixVertexArrows T}
  {base : T.Vertex}
-- given
  (hfollows : cycle.Follows omega) :
-- imply
  ((sixVertexTorusFlip cycle.mask omega).vertical base).toNat = (omega.vertical base).toNat - cycle.verticalFlow base := by
-- proof
  apply StatMech.FrontierD.SixVertexDirectedSimpleCycle.flip_vertical_toNat cycle omega hfollows base

/--
[SixVertexDirectedSimpleCycle.flip_ice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean)
-/
@[path]
private lemma flip_ice_eq
  {T : EvenTorus}
  {cycle : SixVertexDirectedSimpleCycle T}
  {omega : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (hfollows : cycle.Follows omega) :
-- imply
  (sixVertexTorusFlip cycle.mask omega).IceRule := by
-- proof
  apply StatMech.FrontierD.SixVertexDirectedSimpleCycle.flip_ice cycle omega homega hfollows

/--
[SixVertexDirectedSimpleCycle.flip_seamDelta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean)
-/
@[path]
private lemma flip_seamDelta_eq
  {T : EvenTorus}
  {cycle : SixVertexDirectedSimpleCycle T}
  {omega : SixVertexArrows T}
-- given
  (hfollows : cycle.Follows omega) :
-- imply
  sixVertexTorusFlipSeamDelta cycle.mask omega = -∑ column : Fin T.width, cycle.verticalFlow (column, svFinLast T.height_pos) := by
-- proof
  apply StatMech.FrontierD.SixVertexDirectedSimpleCycle.flip_seamDelta cycle omega hfollows

/--
[SixVertexAtMostTwoCycleFamily.singletonCycle_horizontalFlow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean)
-/
@[path]
private lemma singletonCycle_horizontalFlow_eq
  {T : EvenTorus}
  {cycle : SixVertexDirectedSimpleCycle T}
  {base : T.Vertex} :
-- imply
  (SixVertexAtMostTwoCycleFamily.singletonCycle cycle).horizontalFlow base = cycle.horizontalFlow base := by
-- proof
  apply StatMech.FrontierD.SixVertexAtMostTwoCycleFamily.singletonCycle_horizontalFlow cycle base

/--
[SixVertexAtMostTwoCycleFamily.singletonCycle_verticalFlow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean)
-/
@[path]
private lemma singletonCycle_verticalFlow_eq
  {T : EvenTorus}
  {cycle : SixVertexDirectedSimpleCycle T}
  {base : T.Vertex} :
-- imply
  (SixVertexAtMostTwoCycleFamily.singletonCycle cycle).verticalFlow base = cycle.verticalFlow base := by
-- proof
  apply StatMech.FrontierD.SixVertexAtMostTwoCycleFamily.singletonCycle_verticalFlow cycle base

/--
[SixVertexDirectedSimpleCycle.flip_first_pair_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean)
-/
@[path]
private lemma flip_first_pair_related_eq
  {T : EvenTorus}
  {cycle : SixVertexDirectedSimpleCycle T}
  {omega eta : SixVertexArrows T}
-- given
  (hfollows : cycle.Follows omega) :
-- imply
  sixVertexPairAtMostTwoCycleRelated (omega, eta) (sixVertexTorusFlip cycle.mask omega, eta) := by
-- proof
  apply StatMech.FrontierD.SixVertexDirectedSimpleCycle.flip_first_pair_related cycle omega eta hfollows

/--
[SixVertexDirectedSimpleCycle.flip_second_pair_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean)
-/
@[path]
private lemma flip_second_pair_related_eq
  {T : EvenTorus}
  {cycle : SixVertexDirectedSimpleCycle T}
  {omega eta : SixVertexArrows T}
-- given
  (hfollows : cycle.Follows eta) :
-- imply
  sixVertexPairAtMostTwoCycleRelated (omega, eta) (omega, sixVertexTorusFlip cycle.mask eta) := by
-- proof
  apply StatMech.FrontierD.SixVertexDirectedSimpleCycle.flip_second_pair_related cycle omega eta hfollows

/--
[SixVertexAtMostTwoCycleFamily.twoCycles_horizontalFlow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean)
-/
@[path]
private lemma twoCycles_horizontalFlow_eq
  {T : EvenTorus}
  {first second : SixVertexDirectedSimpleCycle T}
  {base : T.Vertex}
-- given
  (hdisjoint : forall a b, (first.edge a).tail != (second.edge b).tail) :
-- imply
  (SixVertexAtMostTwoCycleFamily.twoCycles first second hdisjoint).horizontalFlow base = first.horizontalFlow base + second.horizontalFlow base := by
-- proof
  apply StatMech.FrontierD.SixVertexAtMostTwoCycleFamily.twoCycles_horizontalFlow first second hdisjoint base

/--
[SixVertexAtMostTwoCycleFamily.twoCycles_verticalFlow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean)
-/
@[path]
private lemma twoCycles_verticalFlow_eq
  {T : EvenTorus}
  {first second : SixVertexDirectedSimpleCycle T}
  {base : T.Vertex}
-- given
  (hdisjoint : forall a b, (first.edge a).tail != (second.edge b).tail) :
-- imply
  (SixVertexAtMostTwoCycleFamily.twoCycles first second hdisjoint).verticalFlow base = first.verticalFlow base + second.verticalFlow base := by
-- proof
  apply StatMech.FrontierD.SixVertexAtMostTwoCycleFamily.twoCycles_verticalFlow first second hdisjoint base

/--
[sixVertexDirectedSimpleCycles_flip_pair_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDirectedSimpleCycleFlip.lean)
-/
@[path]
private lemma sixVertexDirectedSimpleCycles_flip_pair_related_eq
  {T : EvenTorus}
  {first second : SixVertexDirectedSimpleCycle T}
  {omega eta : SixVertexArrows T}
-- given
  (hfirst : first.Follows omega)
  (hsecond : second.Follows eta)
  (hdisjoint : forall a b, (first.edge a).tail != (second.edge b).tail) :
-- imply
  sixVertexPairAtMostTwoCycleRelated (omega, eta) (sixVertexTorusFlip first.mask omega, sixVertexTorusFlip second.mask eta) := by
-- proof
  apply StatMech.FrontierD.sixVertexDirectedSimpleCycles_flip_pair_related first second omega eta hfirst hsecond hdisjoint


-- created on 2026-10-23
