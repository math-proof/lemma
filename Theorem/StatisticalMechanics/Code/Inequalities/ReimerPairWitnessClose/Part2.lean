/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyInjClose.Part2
import Def.StatisticalMechanics.Code.Inequalities.ReimerPairWitnessClose.Part2
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


lemma rpw_p1_mem :
    rpw_p1 ∈ {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) |
      p.1 ∈ disjointOccurrence rbi_A rbi_B} := rbi_FF_in_box

lemma rpw_p2_mem :
    rpw_p2 ∈ {p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2) |
      p.1 ∈ disjointOccurrence rbi_A rbi_B} := rbi_FT_in_box


lemma rpw_p1_ne_p2 : rpw_p1 ≠ rpw_p2 := rbi_pairs_ne


theorem rpw_pairDoubleCover_false : ¬ rpw_PairDoubleCover rbi_A rbi_B := by
  rintro ⟨wit, hwitA, hwitB, hinj⟩
  
  obtain ⟨a0, a1⟩ := rbi_force_FF (wit rpw_p1)
    (hwitA rpw_p1 rbi_FF_in_box) (hwitB rpw_p1 rbi_FF_in_box)
  obtain ⟨b0, b1⟩ := rbi_force_FT (wit rpw_p2)
    (hwitA rpw_p2 rbi_FT_in_box) (hwitB rpw_p2 rbi_FT_in_box)
  
  have himg : bfly2 wit rpw_p1 = bfly2 wit rpw_p2 := by
    apply Prod.ext
    · simp only [bfly2_fst, rpw_p1, rpw_p2]
      exact rbi_collision_fst _ _ a0 a1 b0 b1
    · simp only [bfly2_snd, rpw_p1, rpw_p2]
      exact rbi_collision_snd _ _ a0 a1 b0 b1
  exact rpw_p1_ne_p2 (hinj rpw_p1_mem rpw_p2_mem himg)


theorem rpw_pairDoubleCoverAll_false :
    ¬ (∀ (n : ℕ) (A B : Set (ConfigSpace (Fin n))), rpw_PairDoubleCover A B) := by
  intro h
  exact rpw_pairDoubleCover_false (h 2 rbi_A rbi_B)


end StatMech
