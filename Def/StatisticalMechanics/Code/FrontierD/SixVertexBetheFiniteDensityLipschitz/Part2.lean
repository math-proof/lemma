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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteDensityLipschitz


namespace StatMech.FrontierD

noncomputable section

def sixVertexFiniteRootDensityLipschitzConstant (c : Real) : NNReal :=
  Real.toNNReal
    (sixVertexThetaLeftKernelLipschitzBound c / (2 * Real.pi))


end
end StatMech.FrontierD
