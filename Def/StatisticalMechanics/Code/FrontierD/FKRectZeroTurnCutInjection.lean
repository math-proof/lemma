/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutInjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutTopology.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutInjection
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Onsager StatMech.Onsager.BaseCase

noncomputable section

noncomputable def fkRectRightComponentPotential
    (R : FKRectTorus) (eta : R.Configuration) (x : R.Vertex) : Int := by
  classical
  exact if ∃ z : Fin R.height,
    (fkRectOpenGraph R eta).connectedComponentMk x =
      (fkRectOpenGraph R eta).connectedComponentMk
        (fkRectRightColumn R, z) then 1 else 0

end
end StatMech.FrontierD
