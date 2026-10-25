/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusEulerDefect.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNet
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectHorizontalCutGraph (R : FKRectTorus) (omega : R.Configuration) :
    SimpleGraph R.Vertex :=
  (fkRectOpenGraph R omega).deleteEdges (fkRectCrossesHorizontalSeam R)


def fkRectVerticalCutGraph (R : FKRectTorus) (omega : R.Configuration) :
    SimpleGraph R.Vertex :=
  (fkRectOpenGraph R omega).deleteEdges (fkRectCrossesVerticalSeam R)


def FKRectHorizontalWindingWitness (R : FKRectTorus)
    (omega : R.Configuration) (x y : R.Vertex) : Prop :=
  (fkRectOpenGraph R omega).Adj x y ∧
    fkRectCrossesHorizontalSeam R s(x, y) ∧
    (fkRectHorizontalCutGraph R omega).Reachable x y


def FKRectVerticalWindingWitness (R : FKRectTorus)
    (omega : R.Configuration) (x y : R.Vertex) : Prop :=
  (fkRectOpenGraph R omega).Adj x y ∧
    fkRectCrossesVerticalSeam R s(x, y) ∧
    (fkRectVerticalCutGraph R omega).Reachable x y


def fkRectHorizontalSeamIncrement (R : FKRectTorus)
    (x y : R.Vertex) : Int :=
  if x.1.val + 1 = R.width ∧ y.1.val = 0 then 1
  else if x.1.val = 0 ∧ y.1.val + 1 = R.width then -1
  else 0


def fkRectVerticalSeamIncrement (R : FKRectTorus)
    (x y : R.Vertex) : Int :=
  if x.2.val + 1 = R.height ∧ y.2.val = 0 then 1
  else if x.2.val = 0 ∧ y.2.val + 1 = R.height then -1
  else 0


def fkRectWalkWinding (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} : G.Walk x y → Int × Int
  | .nil' _ => (0, 0)
  | .cons' x z _ _ p =>
      (fkRectHorizontalSeamIncrement R x z + (fkRectWalkWinding R p).1,
        fkRectVerticalSeamIncrement R x z + (fkRectWalkWinding R p).2)


def FKRectWindingIndependent (u v : Int × Int) : Prop :=
  u.1 * v.2 - u.2 * v.1 ≠ 0

end
end StatMech.FrontierD
