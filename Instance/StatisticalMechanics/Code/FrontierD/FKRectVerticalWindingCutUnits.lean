/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutUnits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingRankOneReduction
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutTouch.Part2
import Abbrev.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutUnits.Part2
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable instance instFintypeFKRectHorizontalCutCrossingInFiber
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) :
    Fintype (FKRectHorizontalCutCrossingInFiber R omega K) :=
  Fintype.ofFinite _

end
end StatMech.FrontierD
