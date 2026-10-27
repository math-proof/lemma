import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutTouch.Part2
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectForceHorizontalCutClosed_adj_of_not_crossesVerticalSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutTouch.lean)
-/
@[path]
private lemma fkRectForceHorizontalCutClosed_adj_of_not_crossesVerticalSeam_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
-- given
  (hxy : (fkRectOpenGraph R omega).Adj x y)
  (hnot : ¬ fkRectCrossesVerticalSeam R s(x, y)) :
-- imply
  (fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).Adj x y := by
-- proof
  apply StatMech.FrontierD.fkRectForceHorizontalCutClosed_adj_of_not_crossesVerticalSeam R omega hxy hnot

/--
[fkRectTopComponentPotential_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutTouch.lean)
-/
@[path]
private lemma fkRectTopComponentPotential_top_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
  {z : Fin R.width} :
-- imply
  fkRectTopComponentPotential R eta (z, fkRectTopRow R) = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectTopComponentPotential_top R eta z

/--
[exists_fkRectHorizontalCutPrimalCrossingComponent_touched_by_closedWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutTouch.lean)
-/
@[path]
private lemma exists_fkRectHorizontalCutPrimalCrossingComponent_touched_by_closedWalk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex}
  {p : (fkRectOpenGraph R omega).Walk x x}
-- given
  (hwind : (fkRectWalkWinding R p).2 ≠ 0) :
-- imply
  ∃ C : (fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).ConnectedComponent, FKRectHorizontalCutPrimalCrossingComponent R (fkRectForceHorizontalCutClosed R omega) C ∧ ∃ z ∈ p.support, (fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk z = C := by
-- proof
  apply StatMech.FrontierD.exists_fkRectHorizontalCutPrimalCrossingComponent_touched_by_closedWalk R omega p hwind

/--
[exists_horizontalCutCrossing_in_fiber_of_blackBoundaryWinding_snd_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutTouch.lean)
-/
@[path]
private lemma exists_horizontalCutCrossing_in_fiber_of_blackBoundaryWinding_snd_ne_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKRectConfigurationBlackBoundaryCycle R omega}
-- given
  (hwind : (fkRectBlackBoundaryCycleWinding R omega C).2 ≠ 0) :
-- imply
  ∃ X : (fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).ConnectedComponent, FKRectHorizontalCutPrimalCrossingComponent R (fkRectForceHorizontalCutClosed R omega) X ∧ fkRectHorizontalCutComponentTorusComponent R omega X = fkRectBlackBoundaryCyclePrimalComponent R omega C := by
-- proof
  apply StatMech.FrontierD.exists_horizontalCutCrossing_in_fiber_of_blackBoundaryWinding_snd_ne_zero R omega C hwind

/--
[fkRectPrimalComponentHorizontalCutCrossingCount_pos_of_positiveBoundaryMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutTouch.lean)
-/
@[path]
private lemma fkRectPrimalComponentHorizontalCutCrossingCount_pos_of_positiveBoundaryMass_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent}
-- given
  (hmass : 0 < fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K) :
-- imply
  0 < fkRectPrimalComponentHorizontalCutCrossingCount R omega K := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalComponentHorizontalCutCrossingCount_pos_of_positiveBoundaryMass R omega K hmass

/--
[fkRectPositiveBoundaryVerticalMass_le_crossingCount_of_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutTouch.lean)
-/
@[path]
private lemma fkRectPositiveBoundaryVerticalMass_le_crossingCount_of_le_one_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent}
-- given
  (hle : fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K ≤ 1) :
-- imply
  fkRectPrimalComponentPositiveBoundaryVerticalMass R omega K ≤ fkRectPrimalComponentHorizontalCutCrossingCount R omega K := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveBoundaryVerticalMass_le_crossingCount_of_le_one R omega K hle


-- created on 2026-10-23
