/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part8
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexExplicitMarkedPairDecorationEquivFin
    {T : EvenTorus} (omega eta : SixVertexArrows T) (k : Nat) :
    SixVertexExplicitMarkedPairDecoration omega eta k ≃
      Fin (sixVertexMarkedPairMultiplicityNat omega eta k) := by
  apply Fintype.equivOfCardEq
  rw [Fintype.card_fin,
    card_sixVertexExplicitMarkedPairDecoration]


end
end StatMech.FrontierD
