/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc63reroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc62twin.Part2
import Theorem.StatisticalMechanics.Code.Walls.menger_core.Part3
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
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc63b_peel_reconn_single (ends : ι → Sym2 W) :
    ∀ (ds : List ι) (H : Finset ι), gc59_Peelable ends H ds →
      ∀ (o : ι), o ∈ ds.toFinset → ∀ {p q : W}, ends o = s(p, q) →
        connK ends (H \ {o}) p q := by
  intro ds
  induction ds with
  | nil => intro H _ o ho; simp at ho
  | cons h rest ih =>
    intro H hpeel o ho p q hpq
    obtain ⟨hhH, ⟨p', q', hpq', hconn'⟩, hrest⟩ := hpeel
    rw [List.toFinset_cons, Finset.mem_insert] at ho
    rcases ho with rfl | horest
    · 
      
      rw [hpq'] at hpq
      
      rw [Sym2.eq_iff] at hpq
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hconn'
      · exact connK_symm ends _ hconn'
    · 
      have hrec : connK ends ((H \ {h}) \ {o}) p q := ih (H \ {h}) hrest o horest hpq
      refine mng_connK_mono ends ?_ hrec
      intro j hj
      rw [Finset.mem_sdiff, Finset.mem_sdiff] at hj
      rw [Finset.mem_sdiff]
      exact ⟨hj.1.1, hj.2⟩


theorem gc63b_peel_reconn_pair (ends : ι → Sym2 W) :
    ∀ (ds : List ι) (H : Finset ι), gc59_Peelable ends H ds →
      ∀ (a b : ι), a ∈ ds.toFinset → b ∈ ds.toFinset → a ≠ b →
        ∀ {pa qa pb qb : W}, ends a = s(pa, qa) → ends b = s(pb, qb) →
          connK ends (H \ {a, b}) pa qa ∨ connK ends (H \ {a, b}) pb qb := by
  intro ds
  induction ds with
  | nil => intro H _ a b ha; simp at ha
  | cons h rest ih =>
    intro H hpeel a b ha hb hab pa qa pb qb hpa hpb
    obtain ⟨hhH, hhead, hrest⟩ := hpeel
    rw [List.toFinset_cons, Finset.mem_insert] at ha hb
    
    by_cases hha : h = a
    · 
      have hbrest : b ∈ rest.toFinset := by
        rcases hb with hb | hb
        · exact absurd (hb.trans hha) hab.symm
        · exact hb
      
      have hrec : connK ends ((H \ {h}) \ {b}) pb qb :=
        gc63b_peel_reconn_single ends rest (H \ {h}) hrest b hbrest hpb
      refine Or.inr (mng_connK_mono ends ?_ hrec)
      intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨hj.1.1, ?_, hj.2⟩
      rw [← hha]; exact hj.1.2
    · by_cases hhb : h = b
      · 
        have harest : a ∈ rest.toFinset := by
          rcases ha with ha | ha
          · exact absurd (ha.trans hhb) hab
          · exact ha
        have hrec : connK ends ((H \ {h}) \ {a}) pa qa :=
          gc63b_peel_reconn_single ends rest (H \ {h}) hrest a harest hpa
        refine Or.inl (mng_connK_mono ends ?_ hrec)
        intro j hj
        simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨hj.1.1, hj.2, ?_⟩
        rw [← hhb]; exact hj.1.2
      · 
        have harest : a ∈ rest.toFinset := by
          rcases ha with ha | ha
          · exact absurd ha.symm hha
          · exact ha
        have hbrest : b ∈ rest.toFinset := by
          rcases hb with hb | hb
          · exact absurd hb.symm hhb
          · exact hb
        have hrec := ih (H \ {h}) hrest a b harest hbrest hab hpa hpb
        have hsub : (H \ {h}) \ {a, b} ⊆ H \ {a, b} := by
          intro j hj
          rw [Finset.mem_sdiff, Finset.mem_sdiff] at hj
          rw [Finset.mem_sdiff]
          exact ⟨hj.1.1, hj.2⟩
        rcases hrec with hrec | hrec
        · exact Or.inl (mng_connK_mono ends hsub hrec)
        · exact Or.inr (mng_connK_mono ends hsub hrec)


theorem gc63b_minConnector (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι)
    {o x y g : W} (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W)) :
    ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧
      ∀ D', D' ⊆ univ \ K → sources ends D' = ({y, g} : Finset W) → #D ≤ #D' := by
  obtain ⟨P₀, hP₀V, hP₀src⟩ := gc53_exists_fixedPath ends hnd K hoy hog hxy hxg hyg huniv hKsrc
  
  set S : Finset (Finset ι) :=
    (univ \ K).powerset.filter (fun D => sources ends D = ({y, g} : Finset W)) with hS
  have hP₀mem : P₀ ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hP₀V, hP₀src⟩
  have hSne : S.Nonempty := ⟨P₀, hP₀mem⟩
  obtain ⟨D, hDmem, hDmin⟩ := S.exists_min_image (fun D => #D) hSne
  rw [hS, Finset.mem_filter, Finset.mem_powerset] at hDmem
  refine ⟨D, hDmem.1, hDmem.2, ?_⟩
  intro D' hD'V hD'src
  have hD'mem : D' ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hD'V, hD'src⟩
  exact hDmin D' hD'mem


theorem gc63b_disjointConnector_of_reroute (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (h : gc59_RerouteConnector ends K o x y g) :
    gc57_DisjointConnector ends K o x y g :=
  gc59_disjointConnector_of_reroute ends K h


theorem gc63b_countIneq_of_disjointConnector (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc57_DisjointConnector ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc57_countIneq_of_disjointConnector ends hnd hox hoy hog hxy hxg hyg huniv h

end Abstract
end StatMech.Walls
