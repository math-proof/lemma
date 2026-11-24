module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexWidthFreeEnergy.Part4
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries
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

theorem sixVertexAntiferroelectricLambda_pos {c : ℝ} (hc : 2 < c) :
    0 < sixVertexAntiferroelectricLambda c := by
  apply Real.arcosh_pos
  dsimp [sixVertexAntiferroelectricLambda]
  nlinarith

theorem sixVertex_cosh_antiferroelectricLambda {c : ℝ} (hc : 2 < c) :
    Real.cosh (sixVertexAntiferroelectricLambda c) = (c ^ 2 - 2) / 2 := by
  apply Real.cosh_arcosh
  nlinarith


theorem sixVertexAntiferroelectricLambda_unique {c lam : ℝ} (hlam : 0 < lam)
    (hcosh : Real.cosh lam = (c ^ 2 - 2) / 2) :
    lam = sixVertexAntiferroelectricLambda c := by
  rw [sixVertexAntiferroelectricLambda, ← hcosh, Real.arcosh_cosh hlam.le]


end StatMech.FrontierD
