/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexExplicitMarkedDecoratedPairEquiv
    (T : EvenTorus) (left right : Fin (T.width + 1)) (k : Nat) :
    SixVertexExplicitMarkedDecoratedPair T left right k ≃
      SixVertexMarkedDecoratedPair T left right k :=
  Equiv.sigmaCongrRight fun pair =>
    sixVertexExplicitMarkedPairDecorationEquivFin
      pair.1.1 pair.2.1 k

end
end StatMech.FrontierD
