/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsUncond.Part11
import Def.StatisticalMechanics.Code.Ising.PeierlsContourClose.Part3
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


theorem pcc_peierlsContourBound_of_origin (n : ℕ) (β : ℝ)
    (hCount : OriginContourCountBound d n β) :
    PeierlsContourBound d n β :=
  le_trans (pcc_probOriginMinus_le_sum_origin n β) hCount


theorem pcc_peierls_long_range_order_of_origin (hd : 2 ≤ d)
    (hCount : ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → OriginContourCountBound d n β) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
  obtain ⟨β₀, hβ₀⟩ := hCount
  refine peierls_long_range_order' hd ⟨β₀, fun n β hβ => ?_⟩
  exact pcc_peierlsContourBound_of_origin n β (hβ₀ n β hβ)

end Ising
end StatMech
