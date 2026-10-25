/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronLogReduction
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexCanonicalPerronLogEpsilon
    {c : Real} (hc : 2 < c) (k : Nat) : Real :=
  (1 : Real) / (sixVertexPerronGaugeStage hc k : Real) ^ 4

def sixVertexCanonicalPerronLogCutoff
    {c : Real} (hc : 2 < c) (k : Nat) : Nat :=
  (k + 1) / sixVertexPerronGaugeStage hc k + 1

def sixVertexCanonicalPerronRegularizedIntegral
    {c : Real} (hc : 2 < c) (k : Nat) : Real :=
  ∫ y in -Real.pi..Real.pi,
    sixVertexRegularizedBetheLogKernel c
        (sixVertexCanonicalPerronLogEpsilon hc k) y *
      sixVertexFourierPhysicalDensity c hc y

end
end StatMech.FrontierD
