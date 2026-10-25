/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part10
open Finset


namespace StatMech.FrontierD

noncomputable section

def FKColoredStrandSplice.seamDelta
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source) (layer : Bool) : Int :=
  ∑ i : Fin T.width, (
    ((splice.target layer).arrows.vertical
        (i, svFinLast T.height_pos)).toNat -
      ((source layer).arrows.vertical
        (i, svFinLast T.height_pos)).toNat : Int)

end
end StatMech.FrontierD
