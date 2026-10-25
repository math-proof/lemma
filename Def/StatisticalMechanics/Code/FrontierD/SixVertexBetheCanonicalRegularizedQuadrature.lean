/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalRegularizedQuadrature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogTaylor.Part4


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexLogNonperiodicQuadratureError
    (c : Real) (N r : Nat) (lower : Real) (C : NNReal) (F : Real) : Real :=
  (C : Real) * sixVertexFiniteRootDensityUniformBound c *
      ((2 * (r : Real) + 1) / ((N : Real) * lower)) * (2 * Real.pi) +
    (2 * (r : Real) / N) * F + 2 * F / N +
    sixVertexFiniteRootDensityUniformBound c * F *
      ((2 * (r : Real) + 1) / ((N : Real) * lower))

end
end StatMech.FrontierD
