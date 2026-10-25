/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBetheOne.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhase.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexThetaLeftDerivAtZero (c y : Real) : Real :=
  4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y /
    sixVertexThetaDerivativeDenominator c 0 y

end
end StatMech.FrontierD
