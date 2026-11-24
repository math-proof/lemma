module
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationMiddleAffine
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalEval.Part2
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Analytic.OfScalars
public import Theorem.StatisticalMechanics.Code.Onsager.MvSeriesAnalyticUniqueness


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/MvSeriesAnalyticUniqueness.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open BigOperators

open Filter

noncomputable def ons_degreeFiberCoeff
    {E : Type*} (series : MvPowerSeries E ℂ)
    (weight : E → ℂ) (n : ℕ) : ℂ :=
  ∑' m : {m : E →₀ ℕ // Finsupp.degree m = n},
    MvPowerSeries.coeff m.1 series * ons_mvMonomialValue weight m.1

noncomputable def ons_degreeFiberNorm
    {E : Type*} (series : MvPowerSeries E ℂ)
    (weight : E → ℂ) (n : ℕ) : ℝ :=
  ∑' m : {m : E →₀ ℕ // Finsupp.degree m = n},
    ‖MvPowerSeries.coeff m.1 series * ons_mvMonomialValue weight m.1‖

end StatMech.Onsager
