module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy.Part4
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries
open Finset Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable def sixVertexFreeEnergySeriesTerm (lam : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-((n + 1 : ℝ) * lam)) * Real.tanh ((n + 1 : ℝ) * lam) / (n + 1 : ℝ)

end StatMech.FrontierD
