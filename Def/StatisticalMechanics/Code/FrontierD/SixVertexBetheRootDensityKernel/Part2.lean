module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricJacobian.Part3
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootDensityKernel
open Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexRootDensityContractionRate (c : Real) : Real :=
  1 - sixVertexRootDensityKernelFloor c *
    sixVertexRootDensityScale c /
      (sixVertexAnisotropyMagnitude c + 1)

end
end StatMech.FrontierD
