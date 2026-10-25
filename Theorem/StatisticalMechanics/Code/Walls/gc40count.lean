/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc40count.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Walls.gc39threereplica.Part3
import Def.StatisticalMechanics.Code.Walls.gc40count
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)


section Abstract

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc40_sources_compl (ends : ι → Sym2 W) (S : Finset ι) :
    sources ends (univ \ S) = sources ends univ ∆ sources ends S := by
  have h : (univ : Finset ι) \ S = univ ∆ S := by
    ext i; simp only [Finset.mem_sdiff, Finset.mem_symmDiff, Finset.mem_univ, true_and]; tauto
  rw [h, sources_symmDiff]


theorem gc40_sd_oxyg_og {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    ({o, x, y, g} : Finset W) ∆ ({o, g} : Finset W) = ({x, y} : Finset W) := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨h, hn⟩ | ⟨h, hn⟩) <;> tauto
  · rintro (rfl | rfl)
    · exact Or.inl ⟨Or.inr (Or.inl rfl), not_or.2 ⟨fun h => hox h.symm, hxg⟩⟩
    · exact Or.inl ⟨Or.inr (Or.inr (Or.inl rfl)), not_or.2 ⟨fun h => hoy h.symm, hyg⟩⟩


theorem gc40_sd_xy_yg {x y g : W} (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    ({x, y} : Finset W) ∆ ({y, g} : Finset W) = ({x, g} : Finset W) := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨h, hn⟩ | ⟨h, hn⟩) <;> tauto
  · rintro (rfl | rfl)
    · exact Or.inl ⟨Or.inl rfl, not_or.2 ⟨hxy, hxg⟩⟩
    · exact Or.inr ⟨Or.inr rfl, not_or.2 ⟨fun h => hxg h.symm, fun h => hyg h.symm⟩⟩


theorem gc40_sd_xy_xy {o x y g : W} (hxy : x ≠ y) :
    ({x, y} : Finset W) ∆ ({x, y} : Finset W) = (∅ : Finset W) := by
  rw [symmDiff_self]; rfl


theorem gc40_pairCount_reindex
    (P : Finset ι → Prop) [DecidablePred P] (Q : Finset ι → Finset ι → Prop)
    [∀ a, DecidablePred (Q a)] :
    #((univ : Finset (Finset ι × Finset ι)).filter
        (fun p => p.2 ⊆ univ \ p.1 ∧ P p.1 ∧ Q p.1 p.2))
      = ∑ S₁ ∈ (univ : Finset ι).powerset.filter (fun S => P S),
          #((univ \ S₁).powerset.filter (fun S₂ => Q S₁ S₂)) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p => p.1)
    (t := (univ : Finset ι).powerset.filter (fun S => P S))
    (by
      intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq]
      exact ⟨Finset.subset_univ _, hp.2.1⟩)]
  apply Finset.sum_congr rfl
  intro S₁ hS₁
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS₁
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_powerset, Finset.mem_filter]
    obtain ⟨⟨hsub, hP, hQ⟩, hf⟩ := hp
    subst hf
    exact ⟨hsub, hQ⟩
  · intro p hp q hq h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    exact Prod.ext (hp.2.trans hq.2.symm) h
  · intro S₂ hS₂
    simp only [Finset.mem_powerset, Finset.mem_filter] at hS₂
    refine ⟨(S₁, S₂), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨hS₂.1, hS₁.2, hS₂.2⟩, trivial⟩


theorem gc40_inner_drop_third (ends : ι → Sym2 W) (M : Finset ι) {x y g : W}
    (hMsrc : sources ends M = ({x, y} : Finset W)) (hxg : x ≠ g) (hyg : y ≠ g) (hxy : x ≠ y) :
    M.powerset.filter (fun S₂ => sources ends S₂ = ({x, g} : Finset W)
        ∧ sources ends (M \ S₂) = ({y, g} : Finset W))
      = M.powerset.filter (fun S₂ => sources ends S₂ = ({x, g} : Finset W)) := by
  apply Finset.filter_congr
  intro S₂ hS₂
  simp only [Finset.mem_powerset] at hS₂
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  have hcompl : M \ S₂ = M ∆ S₂ := (symmDiff_of_ge hS₂).symm
  rw [hcompl, sources_symmDiff, hMsrc, h]
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨fun h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> tauto, ?_⟩
  rintro (rfl | rfl)
  · exact Or.inl ⟨Or.inr rfl, not_or.2 ⟨fun h => hxy h.symm, hyg⟩⟩
  · exact Or.inr ⟨Or.inr rfl, not_or.2 ⟨fun h => hxg h.symm, fun h => hyg h.symm⟩⟩


theorem gc40_inner_count_collapse (ends : ι → Sym2 W) (M : Finset ι)
    (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) {x y g : W}
    (hMsrc : sources ends M = ({x, y} : Finset W)) (hxg : x ≠ g) (hyg : y ≠ g) (hxy : x ≠ y) :
    #(M.powerset.filter (fun S₂ => sources ends S₂ = ({x, g} : Finset W)))
      = (if connK ends M y g then gc40_E ends M else 0) := by
  have hAxg : ({x, y} : Finset W) ∆ ({y, g} : Finset W) = ({x, g} : Finset W) :=
    gc40_sd_xy_yg hxy hxg hyg
  have sw1 := switching_card ends M hnd ({x, y} : Finset W) hMsrc (u := y) (v := g) hyg
  rw [hAxg] at sw1
  rw [sw1]
  have hAxy : ({x, y} : Finset W) ∆ ({x, y} : Finset W) = (∅ : Finset W) := by rw [symmDiff_self]; rfl
  have sw2 := switching_card ends M hnd ({x, y} : Finset W) hMsrc (u := x) (v := y) hxy
  rw [hAxy] at sw2
  have hxconn : connK ends M x y := by
    apply path_exists ends M hnd x y
    · rw [← mem_sources, hMsrc]; simp
    · intro z hz
      rw [← mem_sources, hMsrc] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz; exact hz
    · exact hxy
  rw [if_pos hxconn] at sw2
  rw [gc40_E, ← sw2]


end Abstract
end StatMech.Walls
