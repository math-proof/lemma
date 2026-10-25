/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part7
import Theorem.StatisticalMechanics.Code.Walls.rc78hallmarriage.Part6
import Def.StatisticalMechanics.Code.Walls.rc76halladaptive
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


theorem swapSet_involutive (L : Finset (Fin n)) : Function.Involutive (swapSet L) := by
  intro p
  unfold swapSet
  ext j <;> simp only [] <;> split_ifs with h <;> rfl


theorem swapSet_bijective (L : Finset (Fin n)) : Function.Bijective (swapSet L) :=
  (swapSet_involutive L).bijective


theorem swapSet_off (L : Finset (Fin n)) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) {j : Fin n}
    (hj : j ∉ L) : (swapSet L p).1 j = p.1 j ∧ (swapSet L p).2 j = p.2 j := by
  refine ⟨?_, ?_⟩ <;> simp only [swapSet, if_neg hj]


theorem swapSet_on (L : Finset (Fin n)) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) {j : Fin n}
    (hj : j ∈ L) : (swapSet L p).1 j = p.2 j ∧ (swapSet L p).2 j = p.1 j := by
  refine ⟨?_, ?_⟩ <;> simp only [swapSet, if_pos hj]


theorem swapSet_singleton (i : Fin n) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    swapSet {i} p = swapAt i p := by
  unfold swapSet swapAt
  ext j <;> simp only [Finset.mem_singleton] <;> split_ifs with h <;> subst_vars <;> rfl


theorem rc76_swapSet_mapsInto_of_witness (A B : Set (ConfigSpace (Fin n)))
    {K L : Finset (Fin n)} (hKL : Disjoint K L) (ω₁ ω₂ : ConfigSpace (Fin n))
    (hA : OccursOn A (K : Set (Fin n)) ω₁) (hB : OccursOn B (L : Set (Fin n)) ω₁) :
    (swapSet L (ω₁, ω₂)).1 ∈ A ∧ (swapSet L (ω₁, ω₂)).2 ∈ B := by
  refine ⟨?_, ?_⟩
  · apply hA
    intro e he
    have heL : e ∉ L := by
      intro hL
      exact (Finset.disjoint_left.mp hKL he) hL
    exact (swapSet_off L (ω₁, ω₂) heL).1
  · apply hB
    intro e he
    rw [Finset.mem_coe] at he
    exact (swapSet_on L (ω₁, ω₂) he).2


theorem rc76_swapSet_mapsInto_singleton (A B : Set (ConfigSpace (Fin n)))
    {K : Finset (Fin n)} {i : Fin n} (hKi : Disjoint K {i}) (ω₁ ω₂ : ConfigSpace (Fin n))
    (hA : OccursOn A (K : Set (Fin n)) ω₁) (hB : OccursOn B ({i} : Finset (Fin n)) ω₁) :
    (swapAt i (ω₁, ω₂)).1 ∈ A ∧ (swapAt i (ω₁, ω₂)).2 ∈ B := by
  rw [← swapSet_singleton i (ω₁, ω₂)]
  exact rc76_swapSet_mapsInto_of_witness A B hKi ω₁ ω₂ hA hB


end StatMech.Walls
