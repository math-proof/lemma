/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFiniteDensityLipschitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootDensityFinite
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheQuadrature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds


namespace StatMech.FrontierD

noncomputable section

def sixVertexThetaLeftKernelLipschitzBound (c : Real) : Real :=
  let d := sixVertexAnisotropyMagnitude c
  4 * d * (d + 1) * (4 * (d + 1) + 2) /
    (16 * (d - 1) ^ 4)

end
end StatMech.FrontierD
