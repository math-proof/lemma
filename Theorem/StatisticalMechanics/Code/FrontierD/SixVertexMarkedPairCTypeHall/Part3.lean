module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairReconnectionWitness
public import Mathlib.Data.Fintype.EquivFin
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part2
open Finset Matrix Polynomial


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

theorem card_sixVertexMarkedDecoratedPairTotalCFiber
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k total : Nat) :
    Fintype.card
        {decorated : SixVertexMarkedDecoratedPair T left right k //
          sixVertexMarkedDecoratedPairTotalC decorated = total} =
      Fintype.card
          {pair : SixVertexMarkedSectorConfiguration T left ×
              SixVertexMarkedSectorConfiguration T right //
            sixVertexConfigurationPairTotalC pair = total} *
        (2 ^ (total - k) * total.choose k) := by
  rw [Fintype.card_congr
    (sixVertexMarkedDecoratedPairTotalCFiberEquiv
      T left right k total)]
  simp


end
end StatMech.FrontierD
