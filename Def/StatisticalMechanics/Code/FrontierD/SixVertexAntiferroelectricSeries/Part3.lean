module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy.Part4
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part2
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

noncomputable def sixVertexFreeEnergySeries (lam : ℝ) : ℝ :=
  ∑' n : ℕ, sixVertexFreeEnergySeriesTerm lam n


noncomputable def sixVertexAntiferroelectricFreeEnergyValue (lam : ℝ) : ℝ :=
  lam / 2 + sixVertexFreeEnergySeries lam


end StatMech.FrontierD
