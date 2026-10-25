/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexCyclicNegEquiv {N : Nat} (hN : 0 < N) : Fin N ≃ Fin N :=
  { toFun := sixVertexCyclicNeg hN
    invFun := sixVertexCyclicNeg hN
    left_inv := sixVertexCyclicNeg_involutive hN
    right_inv := sixVertexCyclicNeg_involutive hN }

end
end StatMech.FrontierD
