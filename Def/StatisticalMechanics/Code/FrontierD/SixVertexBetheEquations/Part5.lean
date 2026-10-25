/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part12
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part4
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def SixVertexSatisfiesBetheEquations
    (c : ℝ) (N n : ℕ) (p : Fin n → ℝ) : Prop :=
  ∀ j, (N : ℝ) * p j =
    2 * Real.pi * sixVertexCentralQuantumNumber j -
      ∑ k, sixVertexTheta c (p j) (p k)


noncomputable def sixVertexBetheUpdate
    (c : ℝ) (N n : ℕ) (p : Fin n → ℝ) (j : Fin n) : ℝ :=
  (2 * Real.pi * sixVertexCentralQuantumNumber j -
    ∑ k, sixVertexTheta c (p j) (p k)) / N


def SixVertexRootSymmetric {n : ℕ} (p : Fin n → ℝ) : Prop :=
  ∀ j, p j.rev = -p j

end
end StatMech.FrontierD
