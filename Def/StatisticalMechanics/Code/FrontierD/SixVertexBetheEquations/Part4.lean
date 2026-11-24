module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part12
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part3
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

def sixVertexCentralQuantumNumber {n : ℕ} (j : Fin n) : ℝ :=
  ((j.val : ℝ) - (j.rev.val : ℝ)) / 2

end
end StatMech.FrontierD
