/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.Comparison
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
open scoped BigOperators
open Module SimpleGraph


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem numClusters_congr_openSub {ω ω' : ConfigSpace (Sym2 V)}
    (h : openSub G ω = openSub G ω') : numClusters G ω = numClusters G ω' := by
  unfold numClusters
  exact Fintype.card_congr (Equiv.cast (by rw [h]))


theorem numClusters_setOpen_le (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) :
    numClusters G (setOpen e ω) ≤ numClusters G (setClosed e ω) := by
  rw [numClusters_eq_finrank, numClusters_eq_finrank]
  apply Submodule.finrank_mono
  intro x hx
  rw [mem_kerLap] at hx ⊢
  intro i j hij
  rw [openSub_adj] at hij
  apply hx
  rw [openSub_adj]
  refine ⟨hij.1, ?_⟩
  have hle := setClosed_le_setOpen e ω s(i, j)
  rw [hij.2] at hle
  exact le_antisymm (by simp) hle


theorem numClusters_setClosed_le_setOpen_succ (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) :
    numClusters G (setClosed e ω) ≤ numClusters G (setOpen e ω) + 1 := by
  by_cases he : e ∈ G.edgeFinset
  · 
    obtain ⟨i0, j0, hadj, heq⟩ : ∃ i j, G.Adj i j ∧ e = s(i, j) := by
      rw [SimpleGraph.mem_edgeFinset] at he
      induction e with
      | h i j => exact ⟨i, j, he, rfl⟩
    rw [numClusters_eq_finrank, numClusters_eq_finrank]
    
    set f : (V → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun x => x i0 - x j0
        map_add' := by intro x y; simp; ring
        map_smul' := by intro c x; simp; ring } with hf
    
    have hkey : kerLap G (setOpen e ω) = kerLap G (setClosed e ω) ⊓ LinearMap.ker f := by
      apply le_antisymm
      · intro x hx
        rw [mem_kerLap] at hx
        refine Submodule.mem_inf.mpr ⟨(mem_kerLap _ _ _).mpr ?_, ?_⟩
        · intro a b hab
          apply hx
          rw [openSub_adj] at hab ⊢
          refine ⟨hab.1, ?_⟩
          have hle := setClosed_le_setOpen e ω s(a, b)
          rw [hab.2] at hle
          exact le_antisymm (by simp) hle
        · rw [LinearMap.mem_ker]
          show x i0 - x j0 = 0
          have hopenadj : (openSub G (setOpen e ω)).Adj i0 j0 := by
            rw [openSub_adj]
            refine ⟨hadj, ?_⟩
            rw [heq]
            exact setOpen_self _ ω
          have := hx i0 j0 hopenadj
          linarith
      · intro x hx
        obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
        rw [mem_kerLap] at hx1 ⊢
        rw [LinearMap.mem_ker] at hx2
        have hx2' : x i0 = x j0 := by have : x i0 - x j0 = 0 := hx2; linarith
        intro a b hab
        rw [openSub_adj] at hab
        by_cases hc : setClosed e ω s(a, b) = true
        · exact hx1 a b ((openSub_adj _ _ _ _).mpr ⟨hab.1, hc⟩)
        · 
          have hsab : s(a, b) = e := by
            by_contra hne
            rw [setClosed_of_ne hne] at hc
            rw [setOpen_of_ne hne] at hab
            exact hc hab.2
          rw [heq, Sym2.eq_iff] at hsab
          rcases hsab with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · subst ha; subst hb; exact hx2'
          · subst ha; subst hb; exact hx2'.symm
    rw [hkey]
    
    have hsub := Submodule.finrank_sup_add_finrank_inf_eq
      (kerLap G (setClosed e ω)) (LinearMap.ker f)
    have htop : finrank ℝ ((kerLap G (setClosed e ω)) ⊔ LinearMap.ker f :
        Submodule ℝ (V → ℝ)) ≤ finrank ℝ (V → ℝ) := Submodule.finrank_le _
    have hkerf : finrank ℝ (V → ℝ) ≤ finrank ℝ (LinearMap.ker f) + 1 := by
      have h1 := LinearMap.finrank_range_add_finrank_ker f
      have h2 : finrank ℝ (LinearMap.range f) ≤ 1 := by
        calc finrank ℝ (LinearMap.range f) ≤ finrank ℝ ℝ := Submodule.finrank_le _
          _ = 1 := by simp
      omega
    omega
  · 
    have hopen_eq : openSub G (setOpen e ω) = openSub G (setClosed e ω) := by
      ext a b
      simp only [openSub_adj]
      constructor
      · rintro ⟨hadj, hopen⟩
        have hne : s(a, b) ≠ e := by
          rintro h
          exact he (by rw [SimpleGraph.mem_edgeFinset, ← h]; exact hadj)
        exact ⟨hadj, by rw [setClosed_of_ne hne]; rw [setOpen_of_ne hne] at hopen; exact hopen⟩
      · rintro ⟨hadj, hopen⟩
        have hne : s(a, b) ≠ e := by
          rintro h
          exact he (by rw [SimpleGraph.mem_edgeFinset, ← h]; exact hadj)
        exact ⟨hadj, by rw [setOpen_of_ne hne]; rw [setClosed_of_ne hne] at hopen; exact hopen⟩
    have : numClusters G (setClosed e ω) = numClusters G (setOpen e ω) :=
      numClusters_congr_openSub G hopen_eq.symm
    omega


theorem openSub_setOpen_eq_setClosed_of_notMem {e : Sym2 V} (he : e ∉ G.edgeFinset)
    (ω : ConfigSpace (Sym2 V)) :
    openSub G (setOpen e ω) = openSub G (setClosed e ω) := by
  ext a b
  simp only [openSub_adj]
  constructor
  · rintro ⟨hadj, hopen⟩
    have hne : s(a, b) ≠ e := fun h => he (by rw [SimpleGraph.mem_edgeFinset, ← h]; exact hadj)
    exact ⟨hadj, by rw [setClosed_of_ne hne]; rw [setOpen_of_ne hne] at hopen; exact hopen⟩
  · rintro ⟨hadj, hopen⟩
    have hne : s(a, b) ≠ e := fun h => he (by rw [SimpleGraph.mem_edgeFinset, ← h]; exact hadj)
    exact ⟨hadj, by rw [setOpen_of_ne hne]; rw [setClosed_of_ne hne] at hopen; exact hopen⟩


end FK
end StatMech
