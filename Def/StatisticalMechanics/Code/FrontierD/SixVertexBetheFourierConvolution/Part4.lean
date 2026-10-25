/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierConvolution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierOrthogonality
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFourierConvolution.Part3


namespace StatMech.FrontierD

noncomputable section

def sixVertexXiRootConvolutionTerm
    (lam : Real) (n : Nat) (alpha : Real) : Real :=
  2 * Real.exp (-2 * ((n + 1 : Real) * lam)) * Real.pi *
    Real.cos ((n + 1 : Real) * alpha) /
      Real.cosh ((n + 1 : Real) * lam)

end
end StatMech.FrontierD
