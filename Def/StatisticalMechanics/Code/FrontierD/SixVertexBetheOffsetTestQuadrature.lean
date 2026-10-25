/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetTestQuadrature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetOperatorQuadrature.Part2


namespace StatMech.FrontierD

open Finset

open Filter Topology

noncomputable section

def sixVertexFixedChargeOffsetTestError
    (c : Real) (N r : Nat) (lower G : Real) (D : NNReal) : Real :=
  (sixVertexOffsetQuotientLipschitzNNReal c lower G D : Real) *
      sixVertexFiniteRootDensityUniformBound c *
      ((2 * (r : Real) + 1) / ((N : Real) * lower)) * (2 * Real.pi) +
    (2 * (r : Real) / N) *
      ((sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) * G / lower)

end
end StatMech.FrontierD
