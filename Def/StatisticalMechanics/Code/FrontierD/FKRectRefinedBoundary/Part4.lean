/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialBoundaryWalk.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundary.Part3


namespace StatMech.FrontierD

noncomputable section

def fkRectRefinedPrimalEdgeStart (R : FKRectTorus) (e : R.EdgeIndex) :
    Int × Int :=
  let p := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1
  (4 * p.1, 4 * p.2)


def fkRectRefinedPrimalEdgeEnd (R : FKRectTorus) (e : R.EdgeIndex) :
    Int × Int :=
  let p := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).2
  (4 * p.1, 4 * p.2)


def fkRectRefinedPrimalEdgeCenter (R : FKRectTorus) (e : R.EdgeIndex) :
    Int × Int :=
  let p := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1
  let q := fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).2
  (2 * (p.1 + q.1), 2 * (p.2 + q.2))


def fkRectRefinedPrimalEdgeDarts (R : FKRectTorus) (e : R.EdgeIndex) :
    List FKRectIntegralSquareDart :=
  let p := fkRectRefinedPrimalEdgeStart R e
  if fkRectClosedPairingAtEdge e then
    [(p, 2), ((p.1 - 1, p.2), 2), ((p.1 - 2, p.2), 2),
      ((p.1 - 3, p.2), 2)]
  else
    [(p, 1), ((p.1, p.2 + 1), 1), ((p.1, p.2 + 2), 1),
      ((p.1, p.2 + 3), 1)]

end
end StatMech.FrontierD
