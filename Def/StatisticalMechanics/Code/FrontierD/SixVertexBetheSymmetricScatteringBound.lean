/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricScatteringBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricTailJacobian.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheKernelQuadrature


namespace StatMech.FrontierD

noncomputable section

def sixVertexSymmetricScatteringPhase
    (c x y : Real) : Real :=
  sixVertexTheta c x y - sixVertexTheta c (-x) y

def sixVertexSymmetricScatteringDerivative
    (c x y : Real) : Real :=
  (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x /
      sixVertexThetaDerivativeDenominator c x y) -
    (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (-x) /
      sixVertexThetaDerivativeDenominator c (-x) y)

def sixVertexSymmetricScatteringLipschitzConstant (c : Real) : NNReal :=
  2 * Real.toNNReal (sixVertexThetaLeftKernelLipschitzBound c)

end
end StatMech.FrontierD
