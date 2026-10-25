/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricJacobian.Part3
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootDensityKernel
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexRootDensityContractionRate (c : Real) : Real :=
  1 - sixVertexRootDensityKernelFloor c *
    sixVertexRootDensityScale c /
      (sixVertexAnisotropyMagnitude c + 1)

end
end StatMech.FrontierD
