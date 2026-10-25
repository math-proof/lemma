/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/RevealmentBoxCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.RevealmentBoundAssembly
import Theorem.StatisticalMechanics.Code.OSSS.CrossMonotone
import Def.StatisticalMechanics.Code.OSSS.RevealmentBoxCrossing.Part2
open scoped BigOperators
open MeasureTheory


namespace StatMech

namespace OSSS

namespace RevealmentBoxCrossing

open OSSS.Monotonic OSSS.AdaptMConditional StatMech.Probability

open StatMech.OSSS.MonotonicFK

open StatMech.OSSS.AdaptDisintegration

open OSSS.GrandCoupling OSSS.Coding

open StatMech.OSSS.RevealmentBoundAssembly

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem truncIndC_succ_eq_reachInd {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (X : ConfigSpace E) (i : ℕ) :
    truncIndC σ f X (i + 1) = reachInd σ f i X := by
  unfold truncIndC reachInd
  by_cases hdet : detAtC (σ : Fin n → E) f X i
  · 
    have hle : stopValC σ f X ≤ i := (cmn_stopValC_le_iff σ f X i).mpr hdet
    rw [if_neg (by omega : ¬ i + 1 ≤ stopValC σ f X), if_pos hdet]
  · 
    
    have hgt : ¬ stopValC σ f X ≤ i := fun h => hdet ((cmn_stopValC_le_iff σ f X i).mp h)
    rw [if_pos (by omega : i + 1 ≤ stopValC σ f X), if_neg hdet]


end RevealmentBoxCrossing
end OSSS
end StatMech
