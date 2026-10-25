/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricDensityJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricJacobian
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteDensityLipschitz.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricDensityJacobian.Part2
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheOddSymmetricJacobianCorrection
    (c : Real) (m : Nat) (q : Fin m → Real) (j : Fin m) : Real :=
  let p := sixVertexOddSymmetricLift m q
  let i := sixVertexOddPositiveIndex m j
  let ir := sixVertexOddNegativeCoordinateIndex m j
  4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p i) /
      sixVertexThetaDerivativeDenominator c (p i) (p i) +
    (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p i) /
      sixVertexThetaDerivativeDenominator c (p i) (p ir))

end
end StatMech.FrontierD
