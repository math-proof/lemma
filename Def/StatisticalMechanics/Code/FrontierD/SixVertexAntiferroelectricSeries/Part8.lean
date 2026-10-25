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
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part7
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable def sixVertexGapSeries (lam : ℝ) : ℝ :=
  -Real.log 2 + ∑' n : ℕ, sixVertexGapCorrectionTerm lam n


end StatMech.FrontierD
