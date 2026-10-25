/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricDensityJacobian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricDominance
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteDensityLipschitz.Part3
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def sixVertexBetheSymmetricJacobianCorrection
    (c : Real) (m : Nat) (q : Fin m → Real) (j : Fin m) : Real :=
  let p := sixVertexEvenSymmetricLift m q
  let i := Fin.natAdd m j
  let ir := Fin.castAdd m j.rev
  4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p i) /
      sixVertexThetaDerivativeDenominator c (p i) (p i) +
    (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (p i) /
      sixVertexThetaDerivativeDenominator c (p i) (p ir))


end
end StatMech.FrontierD
