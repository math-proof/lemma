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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLogFourier


namespace StatMech.FrontierD

open Filter Topology Finset

noncomputable section

def sixVertexRegularizedRapidityLogDerivativeTerm
    (lam epsilon : Real) (n : Nat) (alpha : Real) : Real :=
  let q := sixVertexFreeEnergyRapidityRadius lam
  let r := sixVertexRegularizedRapidityRadius lam epsilon
  (q ^ (n + 1) - r ^ (n + 1)) *
    Real.sin ((n + 1 : Real) * alpha)

def sixVertexRegularizedRapidityLogDerivative
    (lam epsilon alpha : Real) : Real :=
  ∑' n : Nat,
    sixVertexRegularizedRapidityLogDerivativeTerm lam epsilon n alpha

end
end StatMech.FrontierD
