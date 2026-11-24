module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricOffDiagonal.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityComponent
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedDensityCauchy
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheContinuumUniqueness
public import Mathlib.Algebra.Field.Periodic
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricStabilityEstimate.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexFiniteDensityContinuumErrorOfLower
    (c : Real) (N : Nat) (lower : Real) : Real :=
  (sixVertexRootDensityKernelLipschitzBound c *
    sixVertexFiniteRootDensityUniformBound c *
      (1 / ((N : Real) * lower)) * (2 * Real.pi)) / (2 * Real.pi)

end
end StatMech.FrontierD
