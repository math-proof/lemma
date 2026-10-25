/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricJacobian
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteDensityLipschitz.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricDensityJacobian
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexOddPositiveHalfCellLeftIndex
    {m : Nat} (j : Fin m) : Fin ((m + 1) + m) :=
  if hj : j.val = 0 then sixVertexOddCentralIndex m
  else sixVertexOddPositiveIndex m ⟨j.val - 1, by omega⟩

end
end StatMech.FrontierD
