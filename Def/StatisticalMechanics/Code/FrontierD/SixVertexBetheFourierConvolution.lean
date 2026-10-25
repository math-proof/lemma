/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality


namespace StatMech.FrontierD

noncomputable section

def sixVertexXiFourierTerm (lam : Real) (n : Nat) (alpha : Real) : Real :=
  2 * Real.exp (-((n + 1 : Real) * lam)) *
    Real.cos ((n + 1 : Real) * alpha)


def sixVertexXiFourier (lam alpha : Real) : Real :=
  1 + ∑' n : Nat, sixVertexXiFourierTerm lam n alpha

end
end StatMech.FrontierD
