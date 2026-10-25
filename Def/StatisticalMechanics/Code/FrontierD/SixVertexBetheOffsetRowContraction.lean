/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetRowContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetSymmetry
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetOperatorQuadrature.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenRootOffsetBound


namespace StatMech.FrontierD

open Finset

open Filter Topology

noncomputable section

def sixVertexFixedChargeOffsetRowError
    (c : Real) (N r : Nat) (lower : Real) : Real :=
  (sixVertexOffsetQuotientLipschitzNNReal c lower 1 0 : Real) *
      sixVertexFiniteRootDensityUniformBound c *
      ((2 * (r : Real) + 1) / ((N : Real) * lower)) * (2 * Real.pi) +
    (2 * (r : Real) / N) *
      ((sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) / lower)


def sixVertexFixedChargeOffsetContractionMargin (c : Real) : Real :=
  sixVertexRootDensityKernelFloor c * sixVertexRootDensityScale c /
    (4 * (sixVertexAnisotropyMagnitude c + 1) *
      sixVertexFiniteRootDensityUniformBound c)

end
end StatMech.FrontierD
