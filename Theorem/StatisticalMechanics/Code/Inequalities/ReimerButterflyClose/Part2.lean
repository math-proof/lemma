/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerClose2.Part4
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Def.StatisticalMechanics.Code.Inequalities.ReimerButterflyClose
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


theorem rby_downCompress_cexA : Down.compression (0 : Fin 2) rbyCexA = {∅, {0}} := by decide


theorem rby_upCompress_cexB :
    UV.compression ({0} : Finset (Fin 2)) ∅ rbyCexB = {{0}} := by decide


theorem rby_card_boxDoubled_cex : (boxDoubled rbyCexA rbyCexB).card = 2 := by
  rw [card_boxDoubled_eq_dpairsCount]; decide


theorem rby_card_boxDoubled_cex_compressed :
    (boxDoubled (Down.compression (0 : Fin 2) rbyCexA)
      (UV.compression ({0} : Finset (Fin 2)) ∅ rbyCexB)).card = 1 := by
  rw [rby_downCompress_cexA, rby_upCompress_cexB, card_boxDoubled_eq_dpairsCount]; decide


theorem rby_separate_compression_strictly_decreases :
    ∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2),
      (boxDoubled (Down.compression i 𝒜)
        (UV.compression ({i} : Finset (Fin 2)) ∅ ℬ)).card
        < (boxDoubled 𝒜 ℬ).card :=
  ⟨rbyCexA, rbyCexB, 0, by
    rw [rby_card_boxDoubled_cex, rby_card_boxDoubled_cex_compressed]; norm_num⟩


theorem rby_doubleCompress_not_subset_boxDoubled_separate :
    ¬ (doubleCompress (0 : Fin 2) (boxDoubled rbyCexA rbyCexB)
        ⊆ boxDoubled (Down.compression (0 : Fin 2) rbyCexA)
            (UV.compression ({0} : Finset (Fin 2)) ∅ rbyCexB)) := by
  intro hsub
  have hcard := Finset.card_le_card hsub
  rw [doubleCompress_card, rby_card_boxDoubled_cex,
    rby_card_boxDoubled_cex_compressed] at hcard
  omega


end StatMech
