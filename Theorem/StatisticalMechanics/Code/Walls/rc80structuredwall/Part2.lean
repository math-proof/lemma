/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc80structuredwall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc79toporbit.Part4
import Def.StatisticalMechanics.Code.Walls.rc80structuredwall.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


variable {ι : Type*} [Fintype ι] [DecidableEq ι]


variable {κ : Type*} [Fintype κ] [DecidableEq κ]


@[simp] theorem rc80_mem_prodFam {A₁ : Finset (ConfigSpace ι)} {A₂ : Finset (ConfigSpace κ)}
    (w : ConfigSpace (ι ⊕ κ)) :
    w ∈ rc80_prodFam A₁ A₂ ↔ rc80_restL w ∈ A₁ ∧ rc80_restR w ∈ A₂ := by
  simp [rc80_prodFam]


theorem rc80_restL_compl (w : ConfigSpace (ι ⊕ κ)) :
    rc80_restL (rc80_compl w) = rc80_compl (rc80_restL w) := rfl


theorem rc80_restR_compl (w : ConfigSpace (ι ⊕ κ)) :
    rc80_restR (rc80_compl w) = rc80_compl (rc80_restR w) := rfl


theorem rc80_reflInter_prod_card
    (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)) :
    (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card
      = (rc80_reflInterG A₁ B₁).card * (rc80_reflInterG A₂ B₂).card := by
  rw [← Finset.card_product]
  apply Finset.card_bij (fun w _ => (rc80_restL w, rc80_restR w))
  · 
    intro w hw
    simp only [rc80_reflInterG, Finset.mem_filter, rc80_mem_prodFam] at hw
    obtain ⟨⟨hwA1, hwA2⟩, hcompl⟩ := hw
    rw [rc80_restL_compl, rc80_restR_compl] at hcompl
    rw [Finset.mem_product]
    exact ⟨by rw [rc80_reflInterG, Finset.mem_filter]; exact ⟨hwA1, hcompl.1⟩,
           by rw [rc80_reflInterG, Finset.mem_filter]; exact ⟨hwA2, hcompl.2⟩⟩
  · 
    intro w hw v hv h
    rw [Prod.mk.injEq] at h
    obtain ⟨hL, hR⟩ := h
    funext x
    cases x with
    | inl i => exact congrFun hL i
    | inr j => exact congrFun hR j
  · 
    intro q hq
    rw [Finset.mem_product] at hq
    obtain ⟨hqA, hqB⟩ := hq
    rw [rc80_reflInterG, Finset.mem_filter] at hqA hqB
    refine ⟨Sum.elim q.1 q.2, ?_, ?_⟩
    · simp only [rc80_reflInterG, Finset.mem_filter, rc80_mem_prodFam]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · show (fun i => Sum.elim q.1 q.2 (Sum.inl i)) ∈ A₁; simpa using hqA.1
      · show (fun j => Sum.elim q.1 q.2 (Sum.inr j)) ∈ A₂; simpa using hqB.1
      · rw [rc80_restL_compl, rc80_restR_compl]
        refine ⟨?_, ?_⟩
        · show rc80_compl (fun i => Sum.elim q.1 q.2 (Sum.inl i)) ∈ B₁; simpa using hqA.2
        · show rc80_compl (fun j => Sum.elim q.1 q.2 (Sum.inr j)) ∈ B₂; simpa using hqB.2
    · rw [Prod.mk.injEq]
      exact ⟨by funext i; rfl, by funext j; rfl⟩


end StatMech.Walls
