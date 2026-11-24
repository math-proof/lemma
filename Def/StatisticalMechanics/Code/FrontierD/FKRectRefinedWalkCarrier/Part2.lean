module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSquareCoverDartList
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedWalkCarrier.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedWalkCarrier.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def FKRectRefinedWalkCarrier.coverDarts
    {R : FKRectTorus} {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    {h : FKRectSquareWalkLift R w p q}
    (C : FKRectRefinedWalkCarrier R h) :=
  fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
    C.darts C.translation


end
end StatMech.FrontierD
