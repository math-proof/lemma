/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part6
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalEvalAlgebra


namespace StatMech.Onsager

open BigOperators Finset

def ons_MvSeriesEvalSummable
    {E : Type*} (series : MvPowerSeries E ℂ) (weight : E → ℂ) : Prop :=
  Summable fun m : E →₀ ℕ ↦
    ‖MvPowerSeries.coeff m series * ons_mvMonomialValue weight m‖

end StatMech.Onsager
