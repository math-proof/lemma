/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailDensity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteDensityLipschitz.Part3


namespace StatMech.FrontierD

noncomputable section

def sixVertexTailFiniteDensityFloor (c : Real) : Real :=
  (1 - (sixVertexAnisotropyMagnitude c /
    (sixVertexAnisotropyMagnitude c - 1)) / 2) / (2 * Real.pi)

end
end StatMech.FrontierD
