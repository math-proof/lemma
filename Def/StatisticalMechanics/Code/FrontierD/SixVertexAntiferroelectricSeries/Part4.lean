module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy.Part4
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part3
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

noncomputable def sixVertexGapCorrectionTerm (lam : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * (Real.tanh ((n + 1 : ℝ) * lam) - 1) / (n + 1 : ℝ)


end StatMech.FrontierD
