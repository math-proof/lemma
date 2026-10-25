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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable def sixVertexFreeEnergySeriesTerm (lam : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-((n + 1 : ℝ) * lam)) * Real.tanh ((n + 1 : ℝ) * lam) / (n + 1 : ℝ)

end StatMech.FrontierD
