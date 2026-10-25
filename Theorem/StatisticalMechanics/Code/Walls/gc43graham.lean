/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc43graham.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc42countproof.Part2
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


theorem gc43_compl_sources (ends : ι → Sym2 W) (M : Finset ι) :
    sources ends (univ \ M) = sources ends univ ∆ sources ends M :=
  gc40_sources_compl ends M


theorem gc43_sd_oxyg_ox {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    ({o, x, y, g} : Finset W) ∆ ({o, x} : Finset W) = ({y, g} : Finset W) := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : z = o <;> by_cases h2 : z = x <;> by_cases h3 : z = y <;> by_cases h4 : z = g <;>
    subst_vars <;> simp_all


theorem gc43_compl_sources_yg (ends : ι → Sym2 W) (M : Finset ι) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hM : sources ends M = ({o, x} : Finset W)) :
    sources ends (univ \ M) = ({y, g} : Finset W) := by
  rw [gc43_compl_sources, huniv, hM, gc43_sd_oxyg_ox hox hoy hog hxy hxg hyg]


theorem gc43_compl_connK_yg (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (M : Finset ι)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hM : sources ends M = ({o, x} : Finset W)) :
    connK ends (univ \ M) y g := by
  have hCsrc : sources ends (univ \ M) = ({y, g} : Finset W) :=
    gc43_compl_sources_yg ends M hox hoy hog hxy hxg hyg huniv hM
  apply path_exists ends (univ \ M) (fun i _ => hnd i) y g
  · 
    rw [← mem_sources, hCsrc]; simp
  · 
    intro z hz
    rw [← mem_sources, hCsrc] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz; exact hz
  · exact hyg


theorem gc43_exists_reloc_set (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (M : Finset ι)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hM : sources ends M = ({o, x} : Finset W)) :
    ∃ Q ⊆ univ \ M, sources ends Q = ({y, g} : Finset W) := by
  have hconn := gc43_compl_connK_yg ends hnd M hox hoy hog hxy hxg hyg huniv hM
  obtain ⟨Q, hQsub, hQsrc⟩ := exists_conn_set ends (univ \ M) hconn hyg
  exact ⟨Q, hQsub, hQsrc⟩


theorem gc43_connK_mono (ends : ι → Sym2 W) {K K' : Finset ι} (hsub : K ⊆ K') {u v : W}
    (h : connK ends K u v) : connK ends K' u v := by
  refine Relation.ReflTransGen.mono ?_ _ _ h
  rintro a b ⟨i, hi, ha, hb, hne⟩
  exact ⟨i, hsub hi, ha, hb, hne⟩


theorem gc43_ox_conn_of_LHS (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (M : Finset ι)
    {o x : W} (hox : o ≠ x) (hM : sources ends M = ({o, x} : Finset W)) :
    connK ends M o x := by
  apply path_exists ends M (fun i _ => hnd i) o x
  · rw [← mem_sources, hM]; simp
  · intro z hz
    rw [← mem_sources, hM] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz; exact hz
  · exact hox


theorem gc43_yg_conn_of_Q (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (Q : Finset ι)
    {y g : W} (hyg : y ≠ g) (hQ : sources ends Q = ({y, g} : Finset W)) :
    connK ends Q y g := by
  apply path_exists ends Q (fun i _ => hnd i) y g
  · rw [← mem_sources, hQ]; simp
  · intro z hz
    rw [← mem_sources, hQ] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz; exact hz
  · exact hyg


theorem gc43_reloc_sources (ends : ι → Sym2 W) {M Q : Finset ι} (hQsub : Q ⊆ univ \ M)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hM : sources ends M = ({o, x} : Finset W)) (hQ : sources ends Q = ({y, g} : Finset W)) :
    sources ends (M ∪ Q) = ({o, x, y, g} : Finset W) := by
  have hdisj : Disjoint M Q := by
    rw [Finset.disjoint_left]; intro i hiM hiQ
    have := hQsub hiQ; rw [Finset.mem_sdiff] at this; exact this.2 hiM
  have hun : M ∪ Q = M ∆ Q := by rw [Disjoint.symmDiff_eq_sup hdisj]; rfl
  rw [hun, sources_symmDiff, hM, hQ]
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : z = o <;> by_cases h2 : z = x <;> by_cases h3 : z = y <;> by_cases h4 : z = g <;>
    subst_vars <;> simp_all


theorem gc43_reloc_in_RHS (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {M Q : Finset ι}
    (hQsub : Q ⊆ univ \ M) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hM : sources ends M = ({o, x} : Finset W)) (hQ : sources ends Q = ({y, g} : Finset W))
    (hxg_conn : connK ends M x g) :
    sources ends (M ∪ Q) = ({o, x, y, g} : Finset W)
      ∧ connK ends (M ∪ Q) o x ∧ connK ends (M ∪ Q) o y ∧ connK ends (M ∪ Q) o g := by
  
  have hoxM : connK ends M o x := gc43_ox_conn_of_LHS ends hnd M hox hM
  have hygQ : connK ends Q y g := gc43_yg_conn_of_Q ends hnd Q hyg hQ
  have hsubM : M ⊆ M ∪ Q := Finset.subset_union_left
  have hsubQ : Q ⊆ M ∪ Q := Finset.subset_union_right
  have hox' : connK ends (M ∪ Q) o x := gc43_connK_mono ends hsubM hoxM
  have hxg' : connK ends (M ∪ Q) x g := gc43_connK_mono ends hsubM hxg_conn
  have hyg' : connK ends (M ∪ Q) y g := gc43_connK_mono ends hsubQ hygQ
  have hgy' : connK ends (M ∪ Q) g y := StatMech.Sharpness.RandomCurrent.connK_symm ends (M ∪ Q) hyg'
  have hog' : connK ends (M ∪ Q) o g := Relation.ReflTransGen.trans hox' hxg'
  have hoy' : connK ends (M ∪ Q) o y := Relation.ReflTransGen.trans hog' hgy'
  exact ⟨gc43_reloc_sources ends hQsub hox hoy hog hxy hxg hyg hM hQ, hox', hoy', hog'⟩


theorem gc43_E_le_of_subset (ends : ι → Sym2 W) {M N : Finset ι} (hMN : M ⊆ N) :
    gc40_E ends M ≤ gc40_E ends N := by
  rw [gc40_E, gc40_E]
  apply Finset.card_le_card
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
  exact ⟨hS.1.trans hMN, hS.2⟩


theorem gc43_reloc_E_dom (ends : ι → Sym2 W) (M Q : Finset ι) :
    gc40_E ends M ≤ gc40_E ends (M ∪ Q) :=
  gc43_E_le_of_subset ends Finset.subset_union_left


end Abstract
end StatMech.Walls
