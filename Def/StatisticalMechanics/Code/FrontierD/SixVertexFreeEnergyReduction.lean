/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFreeEnergyReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricProduct.Part3
open Filter Topology


namespace StatMech.FrontierD

def SixVertexBethePerronAsymptotics (c lam : ℝ) : Prop :=
  Tendsto (sixVertexCentralWidthRate c) atTop
      (nhds (sixVertexAntiferroelectricFreeEnergyValue lam)) ∧
    ∀ r : ℕ, 1 ≤ r →
      Tendsto (sixVertexFixedChargeLogRatio c r) atTop
        (nhds (-(r : ℝ) * sixVertexAntiferroelectricGapRate lam))


def SixVertexAntiferroelectricTransferConclusion (c lam : ℝ) : Prop :=
  SixVertexHasIteratedLimit (sixVertexBalancedAreaDensity c)
      (sixVertexAntiferroelectricFreeEnergyValue lam) ∧
    ∀ r : ℕ, 1 ≤ r →
      Tendsto (sixVertexFixedChargeRatio c r) atTop
        (nhds (Real.exp (-(r : ℝ) *
          sixVertexAntiferroelectricGapRate lam)))


end StatMech.FrontierD
