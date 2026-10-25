/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailConvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCyclicQuadrature
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailConvolution


namespace StatMech.FrontierD

noncomputable section

def sixVertexRootDensityKernelLipschitzNNReal (c : Real) : NNReal :=
  Real.toNNReal (sixVertexRootDensityKernelLipschitzBound c)

end
end StatMech.FrontierD
