/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Theorem.StatisticalMechanics.Code.Ising.Peierls.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.Ising.PeierlsFull.Part3
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


theorem peierls_long_range_order (hd : 2 ≤ d) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      PeierlsContourBound d n β →
        plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
  obtain ⟨β₀, hβ₀⟩ := exists_beta_peierlsBound_lt_half d
  refine ⟨β₀, fun n β hβ hContour => ?_⟩
  
  have hPlt : probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0 < 1 / 2 :=
    lt_of_le_of_lt hContour (hβ₀ β hβ)
  
  have hmag : 0 < fvMagOrigin (plusField d) n (bondFinsetTouch d n) β 0 :=
    fvMagOrigin_pos_of_probOriginMinus_lt_half _ _ _ _ _ hPlt
  
  exact peierls_lro_criterion hd n β hmag


theorem peierls_long_range_order' (hd : 2 ≤ d)
    (hGeom : ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β → PeierlsContourBound d n β) :
    ∃ β₀ : ℝ, ∀ (n : ℕ) (β : ℝ), β₀ ≤ β →
      plusMeasure d n β 0 ≠ minusMeasure d n β 0 := by
  obtain ⟨β₁, hβ₁⟩ := exists_beta_peierlsBound_lt_half d
  obtain ⟨β₂, hβ₂⟩ := hGeom
  refine ⟨max β₁ β₂, fun n β hβ => ?_⟩
  have h1 : β₁ ≤ β := le_trans (le_max_left _ _) hβ
  have h2 : β₂ ≤ β := le_trans (le_max_right _ _) hβ
  have hPlt : probOriginMinus (plusField d) n (bondFinsetTouch d n) β 0 < 1 / 2 :=
    lt_of_le_of_lt (hβ₂ n β h2) (hβ₁ β h1)
  have hmag : 0 < fvMagOrigin (plusField d) n (bondFinsetTouch d n) β 0 :=
    fvMagOrigin_pos_of_probOriginMinus_lt_half _ _ _ _ _ hPlt
  exact peierls_lro_criterion hd n β hmag

end Ising
end StatMech
