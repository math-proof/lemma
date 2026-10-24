import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutCollision
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectOpenGraph_forceHorizontalCutClosed_le_horizontalCylinderGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutCollision.lean)
-/
@[path]
private lemma fkRectOpenGraph_forceHorizontalCutClosed_le_horizontalCylinderGraph_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega) ≤ fkRectHorizontalCylinderGraph R := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_forceHorizontalCutClosed_le_horizontalCylinderGraph R omega

/--
[fkRectForceHorizontalCutClosedWalk_winding_snd_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutCollision.lean)
-/
@[path]
private lemma fkRectForceHorizontalCutClosedWalk_winding_snd_eq_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
  {p : (fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).Walk x y} :
-- imply
  (fkRectWalkWinding R p).2 = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectForceHorizontalCutClosedWalk_winding_snd_eq_zero R omega p

/--
[exists_closedWalk_winding_snd_eq_of_horizontalCutComponent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutCollision.lean)
-/
@[path]
private lemma exists_closedWalk_winding_snd_eq_of_horizontalCutComponent_eq_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
  {p : (fkRectOpenGraph R omega).Walk x y}
-- given
  (hxy : (fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk x = (fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk y) :
-- imply
  ∃ q : (fkRectOpenGraph R omega).Walk x x, (fkRectWalkWinding R q).2 = (fkRectWalkWinding R p).2 := by
-- proof
  apply StatMech.FrontierD.exists_closedWalk_winding_snd_eq_of_horizontalCutComponent_eq R omega p hxy

/--
[FKRectPrimalComponentHasNet.of_closedWalks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutCollision.lean)
-/
@[path]
private lemma of_closedWalks_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent}
  {x y : R.Vertex}
  {p : (fkRectOpenGraph R omega).Walk x x}
  {q : (fkRectOpenGraph R omega).Walk y y}
-- given
  (hx : (fkRectOpenGraph R omega).connectedComponentMk x = K)
  (hy : (fkRectOpenGraph R omega).connectedComponentMk y = K)
  (hind : FKRectWindingIndependent (fkRectWalkWinding R p) (fkRectWalkWinding R q)) :
-- imply
  FKRectPrimalComponentHasNet R omega K := by
-- proof
  apply StatMech.FrontierD.FKRectPrimalComponentHasNet.of_closedWalks R omega K hx hy p q hind

/--
[fkRectPrimalComponentHasNet_of_primitiveBoundary_cutCollision](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutCollision.lean)
-/
@[path]
private lemma fkRectPrimalComponentHasNet_of_primitiveBoundary_cutCollision_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent}
  {d : FKMedialBlackDart R.medialTorus}
  {x y : R.Vertex}
  {p : (fkRectOpenGraph R omega).Walk x y}
-- given
  (hdK : (fkRectOpenGraph R omega).connectedComponentMk (fkRectMedialDartPrimalLabel R d.1) = K)
  (hprimitive : FKRectPrimitiveWinding (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)))
  (hxK : (fkRectOpenGraph R omega).connectedComponentMk x = K)
  (hxy : (fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk x = (fkRectOpenGraph R (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk y)
  (hboundary : 0 < (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
  (hpath : 0 < (fkRectWalkWinding R p).2)
  (hstrict : (fkRectWalkWinding R p).2 < (fkRectWalkWinding R (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2) :
-- imply
  FKRectPrimalComponentHasNet R omega K := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalComponentHasNet_of_primitiveBoundary_cutCollision R omega K d hdK hprimitive p hxK hxy hboundary hpath hstrict


-- created on 2026-10-23
