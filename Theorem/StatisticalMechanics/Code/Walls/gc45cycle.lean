/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc45cycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc44flow.Part2
import Def.StatisticalMechanics.Code.Walls.gc45cycle
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc45_E_eq_card_evenSub (ends : ι → Sym2 W) (M : Finset ι) :
    gc40_E ends M = #(gc45_evenSub ends M) := rfl


theorem gc45_empty_mem_evenSub (ends : ι → Sym2 W) (M : Finset ι) :
    (∅ : Finset ι) ∈ gc45_evenSub ends M := by
  rw [gc45_evenSub, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨Finset.empty_subset _, ?_⟩
  
  ext z
  simp only [mem_sources, Finset.notMem_empty, iff_false]
  intro hodd
  rw [degK] at hodd
  simp only [Finset.filter_empty, Finset.card_empty] at hodd
  exact (Nat.not_odd_zero hodd)


theorem gc45_evenSub_symmDiff_mem (ends : ι → Sym2 W) (M : Finset ι)
    {S T : Finset ι} (hS : S ∈ gc45_evenSub ends M) (hT : T ∈ gc45_evenSub ends M) :
    S ∆ T ∈ gc45_evenSub ends M := by
  rw [gc45_evenSub, Finset.mem_filter, Finset.mem_powerset] at hS hT ⊢
  refine ⟨?_, ?_⟩
  · 
    intro i hi
    rw [Finset.mem_symmDiff] at hi
    rcases hi with ⟨hiS, _⟩ | ⟨hiT, _⟩
    · exact hS.1 hiS
    · exact hT.1 hiT
  · 
    rw [sources_symmDiff, hS.2, hT.2, symmDiff_self]; rfl


theorem gc45_E_eq_one_of_evenSub_singleton (ends : ι → Sym2 W) (M : Finset ι)
    (h : gc45_evenSub ends M = {(∅ : Finset ι)}) :
    gc40_E ends M = 1 := by
  rw [gc45_E_eq_card_evenSub, h, Finset.card_singleton]


theorem gc45_E_eq_two_of_nullity_one (ends : ι → Sym2 W) (M : Finset ι) {C : Finset ι}
    (hCne : C ≠ (∅ : Finset ι))
    (h : gc45_evenSub ends M = {(∅ : Finset ι), C}) :
    gc40_E ends M = 2 := by
  rw [gc45_E_eq_card_evenSub, h]
  rw [Finset.card_pair (by exact fun heq => hCne heq.symm)]


theorem gc45_fibreDomReloc_of_injOn_subset (ends : ι → Sym2 W) (o x y g : W)
    (φ : Finset ι → Finset ι)
    (hmaps : ∀ M ∈ gc43_Lset ends o x y g, φ M ∈ gc43_Rset ends o x y g)
    (hsub : ∀ M ∈ gc43_Lset ends o x y g, M ⊆ φ M)
    (hinj : Set.InjOn φ (gc43_Lset ends o x y g)) :
    gc43_FibreDomReloc ends o x y g := by
  refine ⟨φ, hmaps, ?_⟩
  intro M' hM'
  set fib := (gc43_Lset ends o x y g).filter (fun M => φ M = M') with hfib
  
  have hcard : #fib ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [hfib, Finset.mem_filter] at ha hb
    exact hinj ha.1 hb.1 (ha.2.trans hb.2.symm)
  obtain ⟨M, hMsub⟩ := Finset.card_le_one_iff_subset_singleton.mp hcard
  by_cases hMmem : M ∈ fib
  · 
    have hfibeq : fib = {M} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hMmem, fun z hz => by
      have := hMsub hz; rwa [Finset.mem_singleton] at this⟩
    rw [hfibeq, Finset.sum_singleton]
    have hML : M ∈ gc43_Lset ends o x y g := by
      rw [hfib, Finset.mem_filter] at hMmem; exact hMmem.1
    have hφM : φ M = M' := by
      rw [hfib, Finset.mem_filter] at hMmem; exact hMmem.2
    have hsubM' : M ⊆ M' := by rw [← hφM]; exact hsub M hML
    exact gc43_E_le_of_subset ends hsubM'
  · 
    have hfibempty : fib = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro z hz
      have := hMsub hz
      rw [Finset.mem_singleton] at this
      rw [this] at hz
      exact hMmem hz
    rw [hfibempty, Finset.sum_empty]
    exact Nat.zero_le _


theorem gc45_FibreDomReloc_of_disjointBridge (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hbridge : gc44_DisjointBridge ends o x y g) :
    gc43_FibreDomReloc ends o x y g := by
  obtain ⟨P, hPsrc, hPdisj⟩ := hbridge
  refine gc45_fibreDomReloc_of_injOn_subset ends o x y g (fun M => M ∆ P) ?_ ?_ ?_
  · 
    intro M hM
    have hMmem := hM
    rw [gc43_Lset, Finset.mem_filter, Finset.mem_powerset] at hMmem
    obtain ⟨_, hMsrc, hMgate⟩ := hMmem
    exact gc44_shift_in_Rset_of_disjoint ends hnd (hPdisj M hM) hox hoy hog hxy hxg hyg
      hMsrc hPsrc hMgate
  · 
    intro M hM
    have hdisj : Disjoint M P := hPdisj M hM
    change M ⊆ M ∆ P
    rw [Disjoint.symmDiff_eq_sup hdisj]
    exact Finset.subset_union_left
  · 
    exact gc44_shift_injOn ends P (gc43_Lset ends o x y g)


end Abstract
end StatMech.Walls
