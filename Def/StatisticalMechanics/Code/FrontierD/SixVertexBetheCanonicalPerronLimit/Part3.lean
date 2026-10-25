/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLogReduction
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLimit.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexCanonicalPerronLipschitzBase (c : Real) : Real :=
  (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2

end
end StatMech.FrontierD
