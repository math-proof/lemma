/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronBulk.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part4
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexCanonicalRegularizationDiagonalEnvelope
    (c eta : Real) : Real :=
  sixVertexCanonicalRegularizationEnvelope c (eta ^ 2) eta

end
end StatMech.FrontierD
