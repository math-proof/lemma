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


namespace StatMech.Onsager

open BigOperators

open Filter

theorem ons_mvMonomialValue_smul
    {E : Type*} [DecidableEq E]
    (s : ℂ) (weight : E → ℂ) (m : E →₀ ℕ) :
    ons_mvMonomialValue (fun e ↦ s * weight e) m =
      s ^ Finsupp.degree m * ons_mvMonomialValue weight m := by
  induction m using Finsupp.induction with
  | zero => simp [ons_mvMonomialValue]
  | single_add e n m he hn ih =>
      rw [ons_mvMonomialValue_add, ons_mvMonomialValue_add,
        map_add, Finsupp.degree_single, pow_add, ih]
      simp [ons_mvMonomialValue, hn]
      ring

end StatMech.Onsager
