/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ConvexGapHC.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.FullRangeHC.Part2
import Def.StatisticalMechanics.Code.Probability.ConvexGapHC
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem cvg_openResidue_of_smallDelta {q : ℝ}
    (H : cvg_smallDeltaResidue q) : frh_openResidue q := by
  intro p hp hp1 E _ _ _ φ u hu0 hu1
  have hp0 : 0 < p := by have := hp.1; linarith
  by_cases hδ : Real.exp (-1) ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
  · exact cvg_openResidue_largeDelta hp0 hp1 φ hδ hu0 hu1
  · rw [not_le] at hδ
    exact H p hp hp1 φ hδ u hu0 hu1


theorem cvg_martingaleHC_of_smallDelta {q : ℝ}
    (H : cvg_smallDeltaResidue q) : mxd_martingaleHC_statement q :=
  frh_martingaleHC_of_openResidue (cvg_openResidue_of_smallDelta H)

end StatMech.Probability
