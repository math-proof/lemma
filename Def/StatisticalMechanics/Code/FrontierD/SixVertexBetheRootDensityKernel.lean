/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootDensityKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricJacobian.Part3
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexRootDensityScale (c : Real) : Real :=
  Real.sqrt (sixVertexAnisotropyMagnitude c ^ 2 - 1)

def sixVertexRootDensityWeight (c x : Real) : Real :=
  sixVertexBetheIntegratingFactor c x / sixVertexRootDensityScale c


def sixVertexRootDensityKernel (c x y : Real) : Real :=
  4 * sixVertexAnisotropyMagnitude c *
      sixVertexBetheIntegratingFactor c x *
      sixVertexBetheIntegratingFactor c y /
    (sixVertexRootDensityScale c *
      sixVertexThetaDerivativeDenominator c x y)


def sixVertexRootDensityKernelFloor (c : Real) : Real :=
  let d := sixVertexAnisotropyMagnitude c
  let s := sixVertexRootDensityScale c
  4 * d * (d - 1) ^ 2 / (s * (4 * (d + 1) ^ 2 + 4))

end
end StatMech.FrontierD
