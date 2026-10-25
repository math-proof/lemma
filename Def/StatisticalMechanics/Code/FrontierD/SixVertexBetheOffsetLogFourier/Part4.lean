/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLogFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronFourierLimit
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLogSingularity.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetProfileRegularity.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLogFourier.Part3


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexOffsetLogFourierQTerm (lam : Real) (n : Nat) : Real :=
  (-1 : Real) ^ (n + 1) * Real.tanh ((n + 1 : Real) * lam) *
    sixVertexFreeEnergyRapidityRadius lam ^ (n + 1) / (n + 1 : Real)

def sixVertexOffsetLogFourierQValue (lam : Real) : Real :=
  ∑' n : Nat, sixVertexOffsetLogFourierQTerm lam n

end
end StatMech.FrontierD
