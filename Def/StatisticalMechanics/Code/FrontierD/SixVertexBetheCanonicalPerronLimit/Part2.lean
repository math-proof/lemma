/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLogReduction
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLimit
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexCanonicalPerronRegularizedBound
    {c : Real} (hc : 2 < c) (k : Nat) : Real :=
  let epsilon := sixVertexCanonicalPerronLogEpsilon hc k
  let f := sixVertexRegularizedBetheLogKernel c epsilon
  let C := sixVertexRegularizedBetheLogLipschitzConstant c epsilon
  |f 0| + (C : Real) * Real.pi


end
end StatMech.FrontierD
