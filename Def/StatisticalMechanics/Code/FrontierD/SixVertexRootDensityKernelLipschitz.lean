/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRootDensityKernelLipschitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailDensity


namespace StatMech.FrontierD

noncomputable section

def sixVertexRootDensityKernelLipschitzBound (c : Real) : Real :=
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  let Q := 4 * (d - 1) ^ 2
  let L := 4 * (d + 1) + 2
  (4 * d * (d + 1) / s) *
    (1 / Q + (d + 1) * L / Q ^ 2)

end
end StatMech.FrontierD
