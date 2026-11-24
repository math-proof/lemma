module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailContinuumEquation


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheContinuumUniqueness.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def SixVertexSatisfiesContinuousDensityEquation
    (c : Real) (rho : Real -> Real) : Prop :=
  ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
    sixVertexRootDensityWeight c x * rho x =
      sixVertexRootDensityWeight c x / (2 * Real.pi) -
        (1 / (2 * Real.pi)) *
          ∫ y in -Real.pi..Real.pi,
            sixVertexRootDensityKernel c x y * rho y


end
end StatMech.FrontierD
