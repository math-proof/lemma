/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigEventLaw.Part2
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


def fkRectCutEdgeEvent (R : FKRectTorus)
    (A : Set R.Configuration) :
    Set (FK.ecz_ClosedOff (fkRectCutGraph R)) :=
  {sigma | ((fkRectCutClosedEdgeConfigEquiv R).symm sigma).1 ∈ A}


end
end StatMech.FrontierD
