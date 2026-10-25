/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part6
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalEvalAlgebra


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_mvMonomialValue_add
    {E : Type*} [DecidableEq E] (weight : E → ℂ)
    (m n : E →₀ ℕ) :
    ons_mvMonomialValue weight (m + n) =
      ons_mvMonomialValue weight m * ons_mvMonomialValue weight n := by
  unfold ons_mvMonomialValue
  apply Finsupp.prod_add_index
  · intro edge hedge
    simp
  · intro edge hedge a b
    rw [pow_add]

theorem ons_mvSeriesEval_eq
    {E : Type*} (series : MvPowerSeries E ℂ) (weight : E → ℂ) :
    ons_mvSeriesEval series weight =
      ∑' m : E →₀ ℕ,
        MvPowerSeries.coeff m series * ons_mvMonomialValue weight m := by
  rfl

end StatMech.Onsager
