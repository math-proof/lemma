module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalCandidateBoundaryLimit
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogTaylor


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogTaylor.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexRegularizedBetheLogNormSecondDerivativeNNReal
    (c epsilon : Real) : NNReal :=
  Real.toNNReal
    (sixVertexRegularizedBetheLogNormSecondDerivativeBound c epsilon)

end
end StatMech.FrontierD
