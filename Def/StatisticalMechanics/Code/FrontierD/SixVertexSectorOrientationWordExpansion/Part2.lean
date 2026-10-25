/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSectorOrientationWordExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorOrientedSplit
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorOrientationWordExpansion
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexOrientationWordTrace
    (N M : Nat) (c : Real) (n : Nat) (word : Fin M -> Bool) : Real :=
  Matrix.trace (matrixOrientationWordProduct
    (sixVertexSectorForwardTransfer N n c) M word)

end
end StatMech.FrontierD
