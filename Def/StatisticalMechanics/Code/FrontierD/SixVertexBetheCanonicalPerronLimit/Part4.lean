/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLogReduction
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLimit.Part3
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexCanonicalPerronDensityBoundConstant
    (c : Real) : Real :=
  (1 / 2 : Real) * |Real.log (c ^ 4)| +
    sixVertexCanonicalPerronLipschitzBase c * Real.pi +
      (2 + Real.pi)

end
end StatMech.FrontierD
