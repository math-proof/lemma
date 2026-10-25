/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricAnalytic.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheJacobianStability.Part4
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricJacobian
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexPositiveHalfRootGap
    {m : Nat} (q : Fin m → Real) (k : Fin m) : Real :=
  if hk : k.val = 0 then 2 * q k
  else q k - q ⟨k.val - 1, by omega⟩

end
end StatMech.FrontierD
