/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairLoopFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part2
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

def sixVertexLoopDecoratedPairTotalC
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) : Nat :=
  sixVertexConfigurationPairTotalC decorated.1


noncomputable def sixVertexMarkedDecoratedPairZeroEquivLoop
    (T : EvenTorus) (left right : Fin (T.width + 1)) :
    SixVertexMarkedDecoratedPair T left right 0 ≃
      SixVertexLoopDecoratedPair T left right where
  toFun decorated :=
    ⟨decorated.1,
      sixVertexZeroDecorationEquivLoopPairings decorated.1 decorated.2⟩
  invFun decorated :=
    ⟨decorated.1,
      (sixVertexZeroDecorationEquivLoopPairings decorated.1).symm
        decorated.2⟩
  left_inv decorated := by
    apply Sigma.ext
    · rfl
    · simp
  right_inv decorated := by
    apply Sigma.ext
    · rfl
    · simp

end
end StatMech.FrontierD
