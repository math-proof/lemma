/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/MvSeriesAnalyticUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationMiddleAffine
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalEval.Part2
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.OfScalars
import Theorem.StatisticalMechanics.Code.Onsager.MvSeriesAnalyticUniqueness.Part2


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
