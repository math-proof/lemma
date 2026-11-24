module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part12
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part6
open Finset Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEquations.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def SixVertexClosedRootSimplex {n : ℕ} (p : Fin n → ℝ) : Prop :=
  Monotone p ∧ SixVertexRootSymmetric p ∧
    ∀ j, -Real.pi ≤ p j ∧ p j ≤ Real.pi


def SixVertexOpenRootSimplex {n : ℕ} (p : Fin n → ℝ) : Prop :=
  StrictMono p ∧ SixVertexRootSymmetric p ∧
    SixVertexRootsInOpenInterval p

end
end StatMech.FrontierD
