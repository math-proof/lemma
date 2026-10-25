/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairCTypeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairReconnectionWitness
import Mathlib.Data.Fintype.EquivFin
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

def sixVertexMarkedDecoratedPairTotalC
    {T : EvenTorus} {left right : Fin (T.width + 1)} {k : Nat}
    (pair : SixVertexMarkedDecoratedPair T left right k) : Nat :=
  sixVertexTorusCTypeCount pair.1.1.1 +
    sixVertexTorusCTypeCount pair.1.2.1


def sixVertexConfigurationPairTotalC
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right) : Nat :=
  sixVertexTorusCTypeCount pair.1.1 +
    sixVertexTorusCTypeCount pair.2.1

end
end StatMech.FrontierD
