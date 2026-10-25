/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronBulk.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part3
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexCanonicalRegularizationEnvelope
    (c epsilon eta : Real) : Real :=
  2 * eta * (Real.log (c ^ 2 / (2 * eta)) + 1) +
    epsilon / (4 * eta)

def sixVertexCanonicalRegularizationUpper
    (c epsilon eta : Real) (k : Nat) : Real :=
  let x := (sixVertexCanonicalLinearEdgeCutoff eta k : Real) /
    (sixVertexFourWidth 0 k : Real)
  2 * x * (Real.log (c ^ 2 / (2 * x)) + 1) +
    epsilon / (4 * x)

end
end StatMech.FrontierD
