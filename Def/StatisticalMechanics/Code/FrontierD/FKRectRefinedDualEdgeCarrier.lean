/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualEdgeCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundary.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3


namespace StatMech.FrontierD

noncomputable section

def fkRectRefinedDualEdgeStart (R : FKRectTorus) (d : R.EdgeIndex) :
    Int × Int :=
  let p := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R d).1
  (4 * p.1 + 2, 4 * p.2 + 2)


def fkRectRefinedDualEdgeEnd (R : FKRectTorus) (d : R.EdgeIndex) :
    Int × Int :=
  let p := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R d).2
  (4 * p.1 + 2, 4 * p.2 + 2)


def fkRectRefinedDualEdgeCenter (R : FKRectTorus) (d : R.EdgeIndex) :
    Int × Int :=
  let p := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R d).1
  let q := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R d).2
  (2 * (p.1 + q.1) + 2, 2 * (p.2 + q.2) + 2)


def fkRectRefinedDualEdgeDarts (R : FKRectTorus) (d : R.EdgeIndex) :
    List FKRectIntegralSquareDart :=
  let p := fkRectRefinedDualEdgeStart R d
  if fkRectClosedPairingAtEdge d then
    [(p, 2), ((p.1 - 1, p.2), 2), ((p.1 - 2, p.2), 2),
      ((p.1 - 3, p.2), 2)]
  else
    [(p, 1), ((p.1, p.2 + 1), 1), ((p.1, p.2 + 2), 1),
      ((p.1, p.2 + 3), 1)]


end
end StatMech.FrontierD
