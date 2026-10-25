/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWeights.Part2
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Def.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part6


namespace StatMech.Onsager

open BigOperators Finset

theorem ons_decoratedFormalKacWardIdentity_eval
    (L : ℕ) [Fact (2 < L)]
    (hformal : ons_decoratedFormalKacWardIdentity L)
    (a b : Fin 2) (decWeight : ons_DecEdge L → ℂ) :
    ons_mvSeriesEval
        (ons_decFormalRoot L ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b)) decWeight =
      ons_decoratedFullWeightedSpinSum L decWeight a b := by
  rw [hformal a b, ons_mvSeriesEval_coe,
    ons_decoratedSpinPolynomial_eval]

end StatMech.Onsager
