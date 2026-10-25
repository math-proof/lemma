/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectIndexedPatternPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

def fkRectPatternOpenEdges (R : FKRectTorus) (I : Finset R.EdgeIndex)
    (eta : R.Configuration) : Finset R.EdgeIndex :=
  I.filter fun a => eta a = true


def fkRectPatternClosedEdges (R : FKRectTorus) (I : Finset R.EdgeIndex)
    (eta : R.Configuration) : Finset R.EdgeIndex :=
  I.filter fun a => eta a = false


def fkRectForceIndexedPattern (R : FKRectTorus) (I : Finset R.EdgeIndex)
    (eta omega : R.Configuration) : R.Configuration :=
  fkRectForceEdgesOpen R (fkRectPatternOpenEdges R I eta)
    (fkRectForceEdgesClosed R (fkRectPatternClosedEdges R I eta) omega)

end
end StatMech.FrontierD
