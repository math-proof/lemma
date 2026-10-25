/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeNonperiodicQuadrature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetTestQuadrature
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeNonperiodicQuadrature
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeNonperiodicOffsetTestError
    (c : Real) (N r : Nat) (lower G : Real) (D : NNReal) : Real :=
  sixVertexFixedChargeOffsetTestError c N r lower G D +
    2 * ((sixVertexAnisotropyMagnitude c /
      (sixVertexAnisotropyMagnitude c - 1)) * G / lower) / N +
    sixVertexFiniteRootDensityUniformBound c *
      ((sixVertexAnisotropyMagnitude c /
        (sixVertexAnisotropyMagnitude c - 1)) * G / lower) *
      ((2 * (r : Real) + 1) / ((N : Real) * lower))


end
end StatMech.FrontierD
