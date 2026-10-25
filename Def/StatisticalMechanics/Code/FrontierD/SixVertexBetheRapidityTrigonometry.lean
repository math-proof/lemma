/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityTrigonometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRapidityMomentum.Part3


namespace StatMech.FrontierD

noncomputable section

def sixVertexRapidityCircle (lam alpha : Real) : Complex :=
  (((Real.cosh lam * Real.cos alpha - 1 : Real) : Complex) +
    ((Real.sinh lam * Real.sin alpha : Real) : Complex) * Complex.I) /
      ((Real.cosh lam - Real.cos alpha : Real) : Complex)


def sixVertexMomentumCircle (lam alpha : Real) : Complex :=
  Complex.exp
    ((sixVertexRapidityMomentum lam alpha : Complex) * Complex.I)

end
end StatMech.FrontierD
