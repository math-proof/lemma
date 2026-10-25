/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy.Part4
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable def sixVertexFreeEnergySeries (lam : ℝ) : ℝ :=
  ∑' n : ℕ, sixVertexFreeEnergySeriesTerm lam n


noncomputable def sixVertexAntiferroelectricFreeEnergyValue (lam : ℝ) : ℝ :=
  lam / 2 + sixVertexFreeEnergySeries lam


end StatMech.FrontierD
