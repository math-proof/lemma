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
import Def.StatisticalMechanics.Code.Ising.PeierlsFull.Part2
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


lemma probOriginMinus_nonneg (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    0 ≤ probOriginMinus η n B β h := by
  unfold probOriginMinus
  apply Finset.sum_nonneg
  intro τ _
  split
  · exact fvProb_nonneg η n B β h τ
  · exact le_refl 0


lemma fvMagOrigin_eq_one_sub_two_mul_probOriginMinus (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ) :
    fvMagOrigin η n B β h = 1 - 2 * probOriginMinus η n B β h := by
  unfold fvMagOrigin probOriginMinus
  rw [Finset.mul_sum, ← fvProb_sum_eq_one η n B β h, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  unfold spin
  by_cases hb : (glue η τ) (origin d) = true <;> simp [hb]; ring


lemma fvMagOrigin_pos_of_probOriginMinus_lt_half (η : ConfigSpace (Site d)) (n : ℕ)
    (B : Finset (Sym2 (Site d))) (β h : ℝ)
    (hP : probOriginMinus η n B β h < 1 / 2) :
    0 < fvMagOrigin η n B β h := by
  rw [fvMagOrigin_eq_one_sub_two_mul_probOriginMinus]
  linarith


end Ising
end StatMech
