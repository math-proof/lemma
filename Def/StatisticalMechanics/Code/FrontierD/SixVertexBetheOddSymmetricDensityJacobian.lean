/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricJacobian
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteDensityLipschitz.Part3
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexOddPositiveHalfRootGap
    {m : Nat} (q : Fin m → Real) (k : Fin m) : Real :=
  if hk : k.val = 0 then q k else q k - q ⟨k.val - 1, by omega⟩

end
end StatMech.FrontierD
