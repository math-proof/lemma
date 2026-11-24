module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part6
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLogReduction
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLimit.Part2
open Finset Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexCanonicalPerronLipschitzBase (c : Real) : Real :=
  (c ^ 2 - 1) / (c ^ 2 - 2) ^ 2

end
end StatMech.FrontierD
