/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitWindingGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnEssential
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part8


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

def fkRectBlackOrbitSubdivisionSide (R : FKRectTorus) : ℕ :=
  8 * R.width * R.height


end
end StatMech.FrontierD
