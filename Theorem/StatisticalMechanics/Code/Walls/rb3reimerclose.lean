/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rb3reimerclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rb2butterflyclose.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc86consolidation
import Def.StatisticalMechanics.Code.Walls.rb3reimerclose
open Finset
open scoped BigOperators NNReal


namespace StatMech.Walls.Reimer

set_option linter.style.longLine false

set_option linter.unusedSimpArgs false


@[simp] lemma rb3_toB_apply {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    rb3_toB S i = decide (i ∈ S) := rfl

@[simp] lemma rb3_mem_ofB {n : ℕ} (x : rbt_Q n) (i : Fin n) :
    i ∈ rb3_ofB x ↔ x i = true := by
  simp [rb3_ofB]

lemma rb3_ofB_toB {n : ℕ} (S : Finset (Fin n)) : rb3_ofB (rb3_toB S) = S := by
  ext i; simp [rb3_mem_ofB, rb3_toB]

lemma rb3_toB_ofB {n : ℕ} (x : rbt_Q n) : rb3_toB (rb3_ofB x) = x := by
  funext i
  simp only [rb3_toB, rb3_mem_ofB]
  cases hx : x i <;> simp [hx]

lemma rb3_toB_injective {n : ℕ} : Function.Injective (rb3_toB (n := n)) := by
  intro S T h
  have := congrArg rb3_ofB h
  rwa [rb3_ofB_toB, rb3_ofB_toB] at this


lemma rb3_toB_compl {n : ℕ} (S : Finset (Fin n)) :
    rbt_antipode (rb3_toB S) = rb3_toB Sᶜ := by
  funext i
  simp only [rbt_antipode, rb3_toB]
  by_cases h : i ∈ S <;> simp [h, Finset.mem_compl]


lemma rb3_inter_eq_iff_agree {n : ℕ} (K S T : Finset (Fin n)) :
    T ∩ K = S ∩ K ↔ ∀ i ∈ K, rb3_toB T i = rb3_toB S i := by
  constructor
  · intro h i hiK
    simp only [rb3_toB, decide_eq_decide]
    constructor
    · intro hiT
      have : i ∈ T ∩ K := Finset.mem_inter.mpr ⟨hiT, hiK⟩
      rw [h] at this; exact (Finset.mem_inter.mp this).1
    · intro hiS
      have : i ∈ S ∩ K := Finset.mem_inter.mpr ⟨hiS, hiK⟩
      rw [← h] at this; exact (Finset.mem_inter.mp this).1
  · intro h
    ext i
    simp only [Finset.mem_inter]
    refine and_congr_left (fun hiK => ?_)
    have := h i hiK
    simp only [rb3_toB, decide_eq_decide] at this
    exact this


end StatMech.Walls.Reimer
