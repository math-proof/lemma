/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingCutTouch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberBalance
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutTouch
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectTopComponentPotential
    (R : FKRectTorus) (eta : R.Configuration) (x : R.Vertex) : Int := by
  classical
  exact if ∃ z : Fin R.width,
    (fkRectOpenGraph R eta).connectedComponentMk x =
      (fkRectOpenGraph R eta).connectedComponentMk
        (z, fkRectTopRow R) then 1 else 0

end
end StatMech.FrontierD
