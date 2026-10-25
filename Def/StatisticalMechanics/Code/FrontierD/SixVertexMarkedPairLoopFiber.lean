/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairLoopFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

def sixVertexCompatibleLoopPairingEquivPi
    {T : EvenTorus} (omega : SixVertexArrows T) :
    SixVertexCompatibleLoopPairing omega ≃
      ((v : T.Vertex) ->
        {pairing : Bool // fkLoopPairingCompatible pairing omega v}) where
  toFun pairing v := ⟨pairing.1 v, pairing.2 v⟩
  invFun choices := ⟨fun v => (choices v).1, fun v => (choices v).2⟩
  left_inv pairing := by
    apply Subtype.ext
    rfl
  right_inv choices := by
    funext v
    apply Subtype.ext
    rfl


end
end StatMech.FrontierD
