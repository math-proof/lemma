/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc44flow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc43graham.Part3
import Def.StatisticalMechanics.Code.Walls.gc44flow
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


theorem gc44_fibreDomReloc_of_injOn_of_E_one (ends : ι → Sym2 W) (o x y g : W)
    (hE : gc44_ForestHyp ends)
    (φ : Finset ι → Finset ι)
    (hmaps : ∀ M ∈ gc43_Lset ends o x y g, φ M ∈ gc43_Rset ends o x y g)
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
  
  have hsum : (∑ M ∈ fib, gc40_E ends M) = #fib := by
    rw [Finset.sum_congr rfl (fun M _ => hE M), Finset.sum_const, smul_eq_mul, mul_one]
  rw [hsum, hE M']
  exact hcard


theorem gc44_sd_ox_yg {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    ({o, x} : Finset W) ∆ ({y, g} : Finset W) = ({o, x, y, g} : Finset W) := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : z = o <;> by_cases h2 : z = x <;> by_cases h3 : z = y <;> by_cases h4 : z = g <;>
    subst_vars <;> simp_all


theorem gc44_shift_sources (ends : ι → Sym2 W) {M P : Finset ι} {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hM : sources ends M = ({o, x} : Finset W)) (hP : sources ends P = ({y, g} : Finset W)) :
    sources ends (M ∆ P) = ({o, x, y, g} : Finset W) := by
  rw [sources_symmDiff, hM, hP, gc44_sd_ox_yg hox hoy hog hxy hxg hyg]


theorem gc44_shift_injOn (ends : ι → Sym2 W) (P : Finset ι) (s : Finset (Finset ι)) :
    Set.InjOn (fun M => M ∆ P) s := by
  intro a ha b hb h
  simp only at h
  have : (a ∆ P) ∆ P = (b ∆ P) ∆ P := by rw [h]
  rwa [symmDiff_symmDiff_cancel_right, symmDiff_symmDiff_cancel_right] at this


theorem gc44_shift_in_Rset_of_disjoint (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {M P : Finset ι} (hdisj : Disjoint M P) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hM : sources ends M = ({o, x} : Finset W)) (hP : sources ends P = ({y, g} : Finset W))
    (hxg_conn : connK ends M x g) :
    M ∆ P ∈ gc43_Rset ends o x y g := by
  
  have hun : M ∆ P = M ∪ P := Disjoint.symmDiff_eq_sup hdisj
  have hPsub : P ⊆ univ \ M := by
    intro i hi
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ i, fun hiM => (Finset.disjoint_left.mp hdisj hiM) hi⟩
  obtain ⟨hsrc', hox', hoy', hog'⟩ :=
    gc43_reloc_in_RHS ends hnd hPsub hox hoy hog hxy hxg hyg hM hP hxg_conn
  rw [gc43_Rset, Finset.mem_filter, Finset.mem_powerset]
  rw [hun]
  exact ⟨Finset.subset_univ _, hsrc', hox', hoy', hog'⟩


end Abstract
end StatMech.Walls
