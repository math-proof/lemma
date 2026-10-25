/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientationWordExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorOrientedSplit
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def matrixOrientationWordProduct {alpha : Type*} [Fintype alpha]
    [DecidableEq alpha] (B : Matrix alpha alpha Real) :
    (M : Nat) -> (Fin M -> Bool) -> Matrix alpha alpha Real
  | 0, _ => 1
  | M + 1, word =>
      (if word 0 then B else Bᵀ) *
        matrixOrientationWordProduct B M (Fin.tail word)

end
end StatMech.FrontierD
