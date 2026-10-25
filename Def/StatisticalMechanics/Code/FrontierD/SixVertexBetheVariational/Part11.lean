/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part7
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational.Part10
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexBethePotential {c : ℝ} (hc : 2 < c) (N n : ℕ)
    (p : Fin n → ℝ) : ℝ :=
  (∑ j, sixVertexBetheOneBodyPotential c N
      (sixVertexCentralQuantumNumber j) (p j)) +
    ∑ j, ∑ k ∈ Finset.Ioi j,
      sixVertexBethePairPotential hc (p j, p k)


def sixVertexBetheOneForm {c : ℝ} (_hc : 2 < c) (N n : ℕ)
    (p : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  (∑ j, (sixVertexBetheOneBodyCoefficient c N
      (sixVertexCentralQuantumNumber j) (p j)) •
        (ContinuousLinearMap.proj j)) +
    ∑ j, ∑ k ∈ Finset.Ioi j,
      (sixVertexBethePairOneForm c (p j, p k)).comp
        ((ContinuousLinearMap.proj j).prod
          (ContinuousLinearMap.proj k))

end
end StatMech.FrontierD
