/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc50threereplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc49nullity2.Part3
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
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  switching_card₂ connK_symm exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc50_sd_ox_ox {o x : W} : ({o, x} : Finset W) ∆ ({o, x} : Finset W) = (∅ : Finset W) := by
  rw [symmDiff_self]; rfl


theorem gc50_sd_oxyg_yg {o x y g : W} (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) :
    ({o, x, y, g} : Finset W) ∆ ({y, g} : Finset W) = ({o, x} : Finset W) :=
  gc49_sd_oxyg_yg hoy hog hxy hxg


theorem gc50_E_eq_oxCount_of_ox_conn (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x : W} (hox : o ≠ x)
    (hm : sources ends m = ({o, x} : Finset W)) :
    gc40_E ends m = #(m.powerset.filter (fun K => sources ends K = ({o, x} : Finset W))) := by
  have hsw := switching_card ends m hnd ({o, x} : Finset W) hm (u := o) (v := x) hox
  rw [gc50_sd_ox_ox] at hsw
  have hoxconn : connK ends m o x := by
    apply path_exists ends m hnd o x
    · rw [← mem_sources, hm]; simp
    · intro z hz
      rw [← mem_sources, hm] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz; exact hz
    · exact hox
  rw [if_pos hoxconn] at hsw
  rw [gc40_E, hsw]


theorem gc50_sd_empty_og_xg {o x g : W} (hox : o ≠ x) (hog : o ≠ g) (hxg : x ≠ g) :
    ((∅ : Finset W) ∆ ({o, g} : Finset W)) ∆ ({x, g} : Finset W) = ({o, x} : Finset W) := by
  rw [show (∅ : Finset W) = (⊥ : Finset W) from rfl, bot_symmDiff]
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨h, hn⟩ | ⟨h, hn⟩) <;> tauto
  · rintro (rfl | rfl)
    · exact Or.inl ⟨Or.inl rfl, not_or.2 ⟨hox, hog⟩⟩
    · exact Or.inr ⟨Or.inl rfl, not_or.2 ⟨fun h => hox h.symm, hxg⟩⟩


theorem gc50_E_eq_oxCount_of_all_conn (ends : ι → Sym2 W) (m : Finset ι)
    {o x g : W} (hox : o ≠ x) (hog : o ≠ g) (hxg : x ≠ g)
    (hconn_ox : connK ends m o x) (hconn_og : connK ends m o g) :
    gc40_E ends m = #(m.powerset.filter (fun K => sources ends K = ({o, x} : Finset W))) := by
  
  have hconn_xg : connK ends m x g :=
    Relation.ReflTransGen.trans
      (StatMech.Sharpness.RandomCurrent.connK_symm ends m hconn_ox) hconn_og
  have hsw := switching_card₂ ends m (∅ : Finset W)
    (u := o) (v := g) (s := x) (t := g) hog hxg hconn_og hconn_xg
  rw [gc50_sd_empty_og_xg hox hog hxg] at hsw
  rw [gc40_E, hsw]


theorem gc50_reindex_by_oxCurrent (ends : ι → Sym2 W) (o x : W) (B Bmox : Finset W)
    (hBmox : B ∆ ({o, x} : Finset W) = Bmox)
    (G : Finset ι → Prop) [DecidablePred G] :
    #(((univ : Finset ι).powerset.filter (fun m => sources ends m = B ∧ G m)).sigma
        (fun m => m.powerset.filter (fun K => sources ends K = ({o, x} : Finset W))))
      = ∑ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
          #((univ \ K).powerset.filter (fun R => sources ends R = Bmox ∧ G (K ∪ R))) := by
  rw [Finset.card_sigma]
  
  
  rw [show (∑ m ∈ (univ : Finset ι).powerset.filter (fun m => sources ends m = B ∧ G m),
          #(m.powerset.filter (fun K => sources ends K = ({o, x} : Finset W))))
      = #((univ : Finset (Finset ι × Finset ι)).filter
          (fun p => p.2 ⊆ p.1 ∧ sources ends p.1 = B ∧ G p.1
            ∧ sources ends p.2 = ({o, x} : Finset W))) from ?_]
  · 
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p => p.2)
      (t := (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)))
      (by
        intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq]
        exact ⟨Finset.subset_univ _, hp.2.2.2⟩)]
    apply Finset.sum_congr rfl
    intro K hK
    simp only [Finset.mem_filter, Finset.mem_powerset] at hK
    
    apply Finset.card_bij (fun p _ => p.1 \ K)
    · 
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨⟨hKsub, hmB, hGm, hKsrc⟩, hp2⟩ := hp
      subst hp2
      simp only [Finset.mem_powerset, Finset.mem_filter]
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        rw [Finset.mem_sdiff] at hi
        exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hi.2⟩
      · 
        have hcompl : p.1 \ p.2 = p.1 ∆ p.2 := (symmDiff_of_ge hKsub).symm
        rw [hcompl, sources_symmDiff, hmB, hKsrc, hBmox]
      · 
        rw [Finset.union_sdiff_of_subset hKsub]; exact hGm
    · 
      intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      obtain ⟨⟨hKa, _, _, _⟩, ha2⟩ := ha
      obtain ⟨⟨hKb, _, _, _⟩, hb2⟩ := hb
      
      have ha1 : a.1 = a.2 ∪ (a.1 \ a.2) := (Finset.union_sdiff_of_subset hKa).symm
      have hb1 : b.1 = b.2 ∪ (b.1 \ b.2) := (Finset.union_sdiff_of_subset hKb).symm
      apply Prod.ext
      · rw [ha1, hb1, ha2, hb2, hab]
      · rw [ha2, hb2]
    · 
      intro R hR
      simp only [Finset.mem_powerset, Finset.mem_filter] at hR
      obtain ⟨hRsub, hRsrc, hGKR⟩ := hR
      refine ⟨(K ∪ R, K), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hdisj : Disjoint K R := by
          rw [Finset.disjoint_left]; intro i hiK hiR
          have := hRsub hiR; rw [Finset.mem_sdiff] at this; exact this.2 hiK
        refine ⟨⟨Finset.subset_union_left, ?_, hGKR, hK.2⟩, trivial⟩
        
        have hun : K ∪ R = K ∆ R := by rw [Disjoint.symmDiff_eq_sup hdisj]; rfl
        rw [hun, sources_symmDiff, hK.2, hRsrc, ← hBmox]
        rw [symmDiff_comm B ({o, x} : Finset W), ← symmDiff_assoc, symmDiff_self, bot_symmDiff]
      · 
        have hdisj : Disjoint K R := by
          rw [Finset.disjoint_left]; intro i hiK hiR
          have := hRsub hiR; rw [Finset.mem_sdiff] at this; exact this.2 hiK
        rw [Finset.union_sdiff_left, Finset.sdiff_eq_self_of_disjoint hdisj.symm]
  · 
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p => p.1)
      (t := (univ : Finset ι).powerset.filter (fun m => sources ends m = B ∧ G m))
      (by
        intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq]
        exact ⟨Finset.subset_univ _, hp.2.1, hp.2.2.1⟩)]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_powerset] at hm
    apply Finset.card_bij (fun K _ => (m, K))
    · intro K hK
      simp only [Finset.mem_powerset, Finset.mem_filter] at hK
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hK.1, hm.2.1, hm.2.2, hK.2⟩, trivial⟩
    · intro a ha b hb hab
      exact congrArg Prod.snd hab
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨⟨hKsub, _, _, hKsrc⟩, hp1⟩ := hp
      refine ⟨p.2, ?_, ?_⟩
      · simp only [Finset.mem_powerset, Finset.mem_filter]
        exact ⟨hp1 ▸ hKsub, hKsrc⟩
      · exact Prod.ext hp1.symm rfl


end Abstract
end StatMech.Walls
