/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricTailJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricDensityJacobian
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailDensity


namespace StatMech.FrontierD

noncomputable section

def sixVertexPositiveHalfCellLeftIndex
    {m : Nat} (j : Fin m) : Fin (m + m) :=
  if hj : j.val = 0 then Fin.castAdd m j.rev
  else Fin.natAdd m ⟨j.val - 1, by omega⟩

end
end StatMech.FrontierD
