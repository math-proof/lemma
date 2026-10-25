/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc61parallelg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.menger_core.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc60exhaustive.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc61_connK_singleton (ends : ι → Sym2 W) {i : ι} {v g : W} (hvg : v ≠ g)
    (hi : ends i = s(v, g)) : connK ends ({i} : Finset ι) v g :=
  Relation.ReflTransGen.single
    ⟨i, Finset.mem_singleton_self i, by rw [hi]; exact Sym2.mem_mk_left v g,
      by rw [hi]; exact Sym2.mem_mk_right v g, hvg⟩


theorem gc61_connK_parallel (ends : ι → Sym2 W) {i j : ι} {v g : W} (hvg : v ≠ g)
    (hi : ends i = s(v, g)) : connK ends ({i, j} : Finset ι) v g :=
  mng_connK_mono ends (by intro k hk; simp only [Finset.mem_singleton] at hk; subst hk; simp)
    (gc61_connK_singleton ends hvg hi)


theorem gc61_sources_singleton (ends : ι → Sym2 W) (i : ι) {v g : W} (hvg : v ≠ g)
    (hi : ends i = s(v, g)) : sources ends ({i} : Finset ι) = ({v, g} : Finset W) := by
  ext x
  simp only [mem_sources, degK, Finset.filter_singleton, Finset.mem_insert, Finset.mem_singleton]
  by_cases hx : x ∈ ends i
  · rw [if_pos hx, Finset.card_singleton]
    have hxvg : x = v ∨ x = g := by
      rw [hi, Sym2.mem_iff] at hx; exact hx
    simp only [show Odd 1 from ⟨0, rfl⟩, true_iff]; exact hxvg
  · rw [if_neg hx, Finset.card_empty]
    have hxvg : ¬ (x = v ∨ x = g) := by
      rintro (rfl | rfl)
      · exact hx (by rw [hi]; exact Sym2.mem_mk_left x g)
      · exact hx (by rw [hi]; exact Sym2.mem_mk_right v x)
    simp only [show ¬ Odd 0 from by decide, false_iff]; exact hxvg


theorem gc61_relative2conn_of_parallel (ends : ι → Sym2 W) {i j : ι} {v g : W}
    (hij : i ≠ j) (hvg : v ≠ g) (hi : ends i = s(v, g)) (hj : ends j = s(v, g))
    (P₁ : Finset ι) (hP₁G : P₁ ⊆ ({i, j} : Finset ι))
    (hP₁src : sources ends P₁ = ({v, g} : Finset W)) :
    connK ends (({i, j} : Finset ι) \ P₁) v g := by
  
  have hgP₁ : Odd (degK ends P₁ g) := by
    rw [← mem_sources, hP₁src]; simp
  
  
  
  
  have hgi : g ∈ ends i := by rw [hi]; exact Sym2.mem_mk_right v g
  have hgj : g ∈ ends j := by rw [hj]; exact Sym2.mem_mk_right v g
  
  by_cases hiP : i ∈ P₁ <;> by_cases hjP : j ∈ P₁
  · 
    exfalso
    have hfilt : P₁.filter (fun k => g ∈ ends k) = {i, j} := by
      apply Finset.Subset.antisymm
      · intro k hk; rw [Finset.mem_filter] at hk
        have := hP₁G hk.1; simpa using this
      · intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact Finset.mem_filter.2 ⟨hiP, hgi⟩
        · exact Finset.mem_filter.2 ⟨hjP, hgj⟩
    have : degK ends P₁ g = 2 := by
      rw [degK, hfilt, Finset.card_insert_of_notMem (by simp [hij]), Finset.card_singleton]
    rw [this] at hgP₁; exact (by decide : ¬ Odd 2) hgP₁
  · 
    have hjmem : j ∈ ({i, j} : Finset ι) \ P₁ := Finset.mem_sdiff.2 ⟨by simp, hjP⟩
    exact mng_connK_mono ends
      (by intro k hk; simp only [Finset.mem_singleton] at hk; subst hk; exact hjmem)
      (gc61_connK_singleton ends hvg hj)
  · 
    have himem : i ∈ ({i, j} : Finset ι) \ P₁ := Finset.mem_sdiff.2 ⟨by simp, hiP⟩
    exact mng_connK_mono ends
      (by intro k hk; simp only [Finset.mem_singleton] at hk; subst hk; exact himem)
      (gc61_connK_singleton ends hvg hi)
  · 
    exfalso
    have hfilt : P₁.filter (fun k => g ∈ ends k) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk; rw [Finset.mem_filter] at hk
      have := hP₁G hk.1; simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · exact hiP hk.1
      · exact hjP hk.1
    have : degK ends P₁ g = 0 := by rw [degK, hfilt, Finset.card_empty]
    rw [this] at hgP₁; exact (by decide : ¬ Odd 0) hgP₁


theorem gc61_two_disjoint_of_parallel (ends : ι → Sym2 W) (hnd : ∀ k : ι, ¬ (ends k).IsDiag)
    {i j : ι} {v g : W} (hij : i ≠ j) (hvg : v ≠ g)
    (hi : ends i = s(v, g)) (hj : ends j = s(v, g)) :
    ∃ P₁ P₂ : Finset ι, P₁ ⊆ ({i, j} : Finset ι) ∧ P₂ ⊆ ({i, j} : Finset ι) ∧ Disjoint P₁ P₂ ∧
      sources ends P₁ = ({v, g} : Finset W) ∧ sources ends P₂ = ({v, g} : Finset W) ∧
      connK ends P₁ v g ∧ connK ends P₂ v g :=
  mng_two_disjoint_connectors ends hnd hvg (gc61_connK_parallel ends hvg hi)
    (fun P₁ hP₁G hP₁src => gc61_relative2conn_of_parallel ends hij hvg hi hj P₁ hP₁G hP₁src)


theorem gc61_parallel_reconnect (ends : ι → Sym2 W) {G : Finset ι} {i j : ι} {v g : W}
    (hij : i ≠ j) (hvg : v ≠ g) (hj : ends j = s(v, g)) (hjG : j ∈ G) :
    connK ends (G \ {i}) v g := by
  have hjmem : j ∈ G \ {i} := Finset.mem_sdiff.2 ⟨hjG, by simp [Ne.symm hij]⟩
  exact mng_connK_mono ends
    (by intro k hk; simp only [Finset.mem_singleton] at hk; subst hk; exact hjmem)
    (gc61_connK_singleton ends hvg hj)


end Abstract
end StatMech.Walls
