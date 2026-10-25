/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc71disjpreserving.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Def.StatisticalMechanics.Code.Walls.rc72configpair
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem graftSwap_involutive (L : Finset (Fin n)) :
    Function.Involutive (graftSwap L) := by
  intro p
  unfold graftSwap
  ext i <;> simp only [] <;> split_ifs <;> rfl


theorem graftSwap_bijective (L : Finset (Fin n)) :
    Function.Bijective (graftSwap L) :=
  (graftSwap_involutive L).bijective


theorem graftSwap_fst_off (L : Finset (Fin n)) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n))
    {i : Fin n} (hi : i ∉ L) : (graftSwap L p).1 i = p.1 i := by
  simp only [graftSwap, hi, if_false]


theorem graftSwap_snd_on (L : Finset (Fin n)) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n))
    {i : Fin n} (hi : i ∈ L) : (graftSwap L p).2 i = p.1 i := by
  simp only [graftSwap, hi, if_true]


theorem graftSwap_mapsInto_of_witness (A B : Set (ConfigSpace (Fin n)))
    {K L : Finset (Fin n)} (hKL : Disjoint K L) (ω₁ ω₂ : ConfigSpace (Fin n))
    (hA : OccursOn A (K : Set (Fin n)) ω₁) (hB : OccursOn B (L : Set (Fin n)) ω₁) :
    (graftSwap L (ω₁, ω₂)).1 ∈ A ∧ (graftSwap L (ω₁, ω₂)).2 ∈ B := by
  refine ⟨?_, ?_⟩
  · 
    apply hA
    intro e he
    have heL : e ∉ L := fun heL => (Finset.disjoint_left.mp hKL he) heL
    exact graftSwap_fst_off L (ω₁, ω₂) heL
  · 
    apply hB
    intro e he
    exact graftSwap_snd_on L (ω₁, ω₂) he


theorem graftSwap_pair_perm (L : Finset (Fin n)) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n))
    (i : Fin n) :
    ((graftSwap L p).1 i, (graftSwap L p).2 i) = (p.1 i, p.2 i)
      ∨ ((graftSwap L p).1 i, (graftSwap L p).2 i) = (p.2 i, p.1 i) := by
  by_cases hi : i ∈ L
  · right; simp only [graftSwap, hi, if_true]
  · left; simp only [graftSwap, hi, if_false]


theorem graftSwap_jointCount (L : Finset (Fin n)) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    (Finset.univ.filter (fun i => (graftSwap L p).1 i = true)).card
        + (Finset.univ.filter (fun i => (graftSwap L p).2 i = true)).card
      = (Finset.univ.filter (fun i => p.1 i = true)).card
        + (Finset.univ.filter (fun i => p.2 i = true)).card := by
  
  rw [← Finset.card_union_add_card_inter, ← Finset.card_union_add_card_inter]
  
  have key : ∀ i : Fin n,
      (if (graftSwap L p).1 i = true then 1 else 0) + (if (graftSwap L p).2 i = true then 1 else 0)
        = (if p.1 i = true then 1 else 0) + (if p.2 i = true then 1 else 0) := by
    intro i
    rcases graftSwap_pair_perm L p i with h | h
    · simp only [Prod.mk.injEq] at h; rw [h.1, h.2]
    · simp only [Prod.mk.injEq] at h; rw [h.1, h.2]; ring
  
  have card_as_sum : ∀ (q : ConfigSpace (Fin n)),
      (Finset.univ.filter (fun i => q i = true)).card
        = ∑ i : Fin n, (if q i = true then 1 else 0) := by
    intro q
    rw [Finset.card_filter]
  rw [Finset.card_union_add_card_inter, Finset.card_union_add_card_inter,
    card_as_sum, card_as_sum, card_as_sum, card_as_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => key i)


end StatMech.Walls
