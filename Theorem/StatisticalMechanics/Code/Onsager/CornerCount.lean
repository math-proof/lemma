/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CornerCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WindingAssembly.Part2
import Def.StatisticalMechanics.Code.Onsager.CornerCount


namespace StatMech.Onsager.CornerCount

open StatMech.Onsager.WindingAssembly

open StatMech.Onsager.SplitConstruction


theorem bigSquare_cc : ccCount bigSquare = 0 := by decide

theorem bigSquare_rc : rcCount bigSquare = 0 := by decide

theorem bigSquare_simple : simplePred bigSquare := by
  refine ⟨by decide, ?_, ?_⟩
  · 
    unfold bigSquare isAxisAligned
    refine List.IsChain.cons ?_ ?_
    refine List.IsChain.cons ?_ ?_
    refine List.IsChain.cons ?_ ?_
    · exact List.isChain_singleton _
    · intro y hy; simp at hy; subst hy; right; rfl
    · intro y hy; simp at hy; subst hy; left; rfl
    · intro y hy; simp at hy; subst hy; right; rfl
  · 
    intro x hx y hy
    simp only [bigSquare, List.getLast?, List.head?] at hx hy
    rw [Option.mem_some_iff] at hx hy
    subst hx; subst hy; left; rfl


theorem hbase_false :
    ¬ (∀ V : List Pt, simplePred V → rcCount V = 0 → ccCount V = 4) := by
  intro h
  have := h bigSquare bigSquare_simple bigSquare_rc
  rw [bigSquare_cc] at this
  exact absurd this (by decide)


theorem sum_eq_ccrc (L : List ℤ) (h : ∀ t ∈ L, t = -1 ∨ t = 0 ∨ t = 1) :
    L.sum = ((L.countP (fun t => t == 1) : ℕ) : ℤ) - ((L.countP (fun t => t == -1) : ℕ) : ℤ) := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have hmem : ∀ x ∈ t, x = -1 ∨ x = 0 ∨ x = 1 := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ha := h a (List.mem_cons_self ..)
    rw [List.sum_cons, List.countP_cons, List.countP_cons, ih hmem]
    rcases ha with ha | ha | ha <;> subst ha <;> push_cast <;> simp <;> ring


end StatMech.Onsager.CornerCount
