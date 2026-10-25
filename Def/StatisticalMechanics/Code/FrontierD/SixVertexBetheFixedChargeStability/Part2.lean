/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeStability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricStabilityEstimate.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheInfiniteAnisotropyGauge
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeStability.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeFiniteDensityContinuumErrorOfLower
    (c : Real) (N r : Nat) (lower : Real) : Real :=
  (sixVertexRootDensityKernelLipschitzBound c *
      sixVertexFiniteRootDensityUniformBound c *
      ((2 * (r : Real) + 1) / ((N : Real) * lower)) *
        (2 * Real.pi) +
    (2 * (r : Real) / N) * sixVertexRootDensityKernelUniformBound c) /
      (2 * Real.pi)

def sixVertexFixedChargeDensityStabilityErrorOfLower
    (c : Real) (N r : Nat) (lower : Real) : Real :=
  sixVertexRootDensityContractionRate c *
      (((r : Real) / N) / (2 * Real.pi) *
        ((sixVertexAnisotropyMagnitude c + 1) /
          sixVertexRootDensityScale c)) +
    (((r : Real) / N) / (2 * Real.pi)) *
      sixVertexRootDensityKernelUniformBound c +
    sixVertexFixedChargeFiniteDensityContinuumErrorOfLower c N r lower

end
end StatMech.FrontierD
