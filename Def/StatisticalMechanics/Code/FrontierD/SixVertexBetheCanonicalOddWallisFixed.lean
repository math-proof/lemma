/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallis.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisFixed


namespace StatMech.FrontierD

open Filter Topology Finset MeasureTheory

noncomputable section

def sixVertexBetheDesingularizedLogObservableDerivative
    (c x : Real) : Real :=
  -(c ^ 2 - 1) * Real.sin x /
      ((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos x) -
    (1 / 2 : Real) *
      (sixVertexSincDerivative (x / 2) / Real.sinc (x / 2))

end
end StatMech.FrontierD
