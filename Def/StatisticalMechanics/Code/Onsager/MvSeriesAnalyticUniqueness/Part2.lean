module
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationMiddleAffine
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalEval.Part2
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Analytic.OfScalars
public import Theorem.StatisticalMechanics.Code.Onsager.MvSeriesAnalyticUniqueness.Part2


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

noncomputable def ons_degreeFiberPolynomial
    {E : Type*} [Fintype E] [DecidableEq E]
    (series : MvPowerSeries E ℂ) (n : ℕ) : MvPolynomial E ℂ :=
  ∑ m ∈ (Finsupp.finite_of_degree_le (σ := E) n).toFinset.filter
      (fun m ↦ Finsupp.degree m = n),
    MvPolynomial.monomial m (MvPowerSeries.coeff m series)

end StatMech.Onsager
