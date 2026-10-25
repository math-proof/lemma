/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteKeyCapacityMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall.Part4
import Def.StatisticalMechanics.Code.FrontierD.FiniteKeyCapacityMatching
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sigmaFinFiberCard
    {Key : Type*} [Fintype Key] [DecidableEq Key]
    (capacity : Key -> Nat) (key : Key) :
    Fintype.card
        {source : FiniteKeyCapacityCopies Key capacity // source.1 = key} =
      capacity key := by
  rw [Fintype.card_congr (sigmaFinFiberEquiv capacity key)]
  exact Fintype.card_fin _


end
end StatMech.FrontierD
