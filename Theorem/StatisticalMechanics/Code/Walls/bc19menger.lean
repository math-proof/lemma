/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc19menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc18mengerhard.Part3
import Structure.StatisticalMechanics.Code.Walls.bc19menger


namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}


omit [DecidableEq V] in

theorem bc19_AFan_c_inj {A S R : Set V} (F : bc19_AFan G A S R k) :
    Function.Injective F.c := by
  intro i j hij
  by_contra hne
  have hi : F.c i ∈ (F.q i).support := (F.q i).end_mem_support
  have hj : F.c j ∈ (F.q j).support := (F.q j).end_mem_support
  have hj' : F.c i ∈ (F.q j).support := by rw [hij]; exact hj
  exact F.hdisj hne hi hj'

omit [DecidableEq V] in

theorem bc19_AFan_c_cover [Fintype V] {A S R : Set V} (hS : S.ncard = k)
    (F : bc19_AFan G A S R k) : ∀ s ∈ S, ∃ i, F.c i = s := by
  have hinj := bc19_AFan_c_inj F
  set T := Set.range F.c with hT
  have hTsub : T ⊆ S := by rintro _ ⟨i, rfl⟩; exact F.hc i
  have hTcard : T.ncard = k := by
    rw [hT, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hTeq : T = S := Set.eq_of_subset_of_ncard_le hTsub (by rw [hTcard, hS]) (Set.toFinite S)
  intro s hs
  rw [← hTeq] at hs; obtain ⟨i, hi⟩ := hs; exact ⟨i, hi⟩


end StatMech.Walls
