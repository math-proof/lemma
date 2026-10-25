/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairDecoratedHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairFractionalTransport.Part3
import Theorem.StatisticalMechanics.Code.Foundations.FiniteBidegreeHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

abbrev SixVertexMarkedDecoratedPair
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :=
  Sigma fun pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right =>
    Fin (sixVertexMarkedPairMultiplicityNat pair.1.1 pair.2.1 k)


end
end StatMech.FrontierD
