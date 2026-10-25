/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.STT.Part4
import Def.StatisticalMechanics.Code.Universality.STTTransport.Part2
open SimpleGraph


namespace StatMech

namespace Universality

variable {V : Type*}


variable (E : SimpleGraph V) {A B C : V}


theorem reach_tri_to_star (A B C O : V) (ωt ωs : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hOA : O ≠ A) (hOB : O ≠ B) (hOC : O ≠ C)
    (hm : MatchesPattern ωt ωs) {u v : V}
    (h : (E ⊔ triCell A B C ωt).Reachable u v) :
    (E ⊔ starCell A B C O ωs).Reachable u v := by
  obtain ⟨hmAB, hmAC, hmBC⟩ := hm
  refine reach_collapse _ _ id ?_ rfl rfl h
  intro a b hab
  simp only [id]
  rcases hab with hE | hcell
  · exact Adj.reachable (Or.inl hE)
  · 
    rcases triCell_adj_imp A B C ωt hcell with ⟨hb, he⟩ | ⟨hb, he⟩ | ⟨hb, he⟩
    · 
      have hstar : starBC ωs = true := by
        rw [← hmBC]; unfold triBC; simp [hb]
      have r := starCell_reach_BC E A B C O ωs hOB hOC hstar
      rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact r
      · exact r.symm
    · have hstar : starAC ωs = true := by
        rw [← hmAC]; unfold triAC; simp [hb]
      have r := starCell_reach_AC E A B C O ωs hOA hOC hstar
      rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact r
      · exact r.symm
    · have hstar : starAB ωs = true := by
        rw [← hmAB]; unfold triAB; simp [hb]
      have r := starCell_reach_AB E A B C O ωs hOA hOB hstar
      rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact r
      · exact r.symm


theorem reach_star_to_tri (A B C O : V) (ωt ωs : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hOA : O ≠ A) (hOB : O ≠ B) (hOC : O ≠ C)
    (hm : MatchesPattern ωt ωs)
    (hEO : ∀ x, ¬ E.Adj x O) {u v : V} (hu : u ≠ O) (hv : v ≠ O)
    (h : (E ⊔ starCell A B C O ωs).Reachable u v) :
    (E ⊔ triCell A B C ωt).Reachable u v := by
  obtain ⟨hmAB, hmAC, hmBC⟩ := hm
  
  have triAB' : starAB ωs = true → (E ⊔ triCell A B C ωt).Reachable A B := fun hs =>
    triCell_reach_AB E A B C ωt hAB hAC hBC (by rw [hmAB]; exact hs)
  have triAC' : starAC ωs = true → (E ⊔ triCell A B C ωt).Reachable A C := fun hs =>
    triCell_reach_AC E A B C ωt hAB hAC hBC (by rw [hmAC]; exact hs)
  have triBC' : starBC ωs = true → (E ⊔ triCell A B C ωt).Reachable B C := fun hs =>
    triCell_reach_BC E A B C ωt hAB hAC hBC (by rw [hmBC]; exact hs)
  refine bypass_vertex _ _ O ?_ ?_ hu hv h
  · 
    intro a b ha hb hab
    rcases hab with hE | hcell
    · exact Adj.reachable (Or.inl hE)
    · rcases starCell_adj_imp A B C O ωs hcell with ⟨hO, _⟩ | ⟨hO, _⟩
      · exact absurd hO ha
      · exact absurd hO hb
  · 
    intro s t hs ht hsO hOt
    
    have hspoke : ∀ {p : V}, (E ⊔ starCell A B C O ωs).Adj p O → p ≠ O →
        (p = A ∧ ωs.1 = true) ∨ (p = B ∧ ωs.2.1 = true) ∨ (p = C ∧ ωs.2.2 = true) := by
      intro p hpO hpne
      rcases hpO with hE | hcell
      · exact absurd hE (hEO p)
      · rcases starCell_adj_imp A B C O ωs hcell with ⟨hO, _⟩ | ⟨_, hcase⟩
        · exact absurd hO hpne
        · rcases hcase with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩
          · exact Or.inl ⟨rfl, hb⟩
          · exact Or.inr (Or.inl ⟨rfl, hb⟩)
          · exact Or.inr (Or.inr ⟨rfl, hb⟩)
    have hsp_s := hspoke hsO hs
    have hsp_t := hspoke hOt.symm ht
    
    rcases hsp_s with ⟨rfl, hsb⟩ | ⟨rfl, hsb⟩ | ⟨rfl, hsb⟩ <;>
      rcases hsp_t with ⟨rfl, htb⟩ | ⟨rfl, htb⟩ | ⟨rfl, htb⟩
    
    · exact Reachable.refl _
    · exact triAB' (by unfold starAB; simp [hsb, htb])
    · exact triAC' (by unfold starAC; simp [hsb, htb])
    · exact (triAB' (by unfold starAB; simp [hsb, htb])).symm
    · exact Reachable.refl _
    · exact triBC' (by unfold starBC; simp [hsb, htb])
    · exact (triAC' (by unfold starAC; simp [hsb, htb])).symm
    · exact (triBC' (by unfold starBC; simp [hsb, htb])).symm
    · exact Reachable.refl _


theorem starTriangle_reach_iff (A B C O : V) (ωt ωs : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hOA : O ≠ A) (hOB : O ≠ B) (hOC : O ≠ C)
    (hm : MatchesPattern ωt ωs) (hEO : ∀ x, ¬ E.Adj x O) {u v : V} (hu : u ≠ O) (hv : v ≠ O) :
    (E ⊔ triCell A B C ωt).Reachable u v ↔ (E ⊔ starCell A B C O ωs).Reachable u v :=
  ⟨reach_tri_to_star E A B C O ωt ωs hAB hAC hBC hOA hOB hOC hm,
   reach_star_to_tri E A B C O ωt ωs hAB hAC hBC hOA hOB hOC hm hEO hu hv⟩


theorem starTriangle_crossing_transport (A B C O : V) (ωt ωs : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hOA : O ≠ A) (hOB : O ≠ B) (hOC : O ≠ C)
    (hm : MatchesPattern ωt ωs) (hEO : ∀ x, ¬ E.Adj x O) {u v : V} (hu : u ≠ O) (hv : v ≠ O) :
    (∃ p q : V, p = u ∧ q = v ∧ (E ⊔ triCell A B C ωt).Reachable p q) ↔
    (∃ p q : V, p = u ∧ q = v ∧ (E ⊔ starCell A B C O ωs).Reachable p q) := by
  constructor
  · rintro ⟨p, q, rfl, rfl, hpq⟩
    exact ⟨p, q, rfl, rfl,
      (starTriangle_reach_iff E A B C O ωt ωs hAB hAC hBC hOA hOB hOC hm hEO hu hv).1 hpq⟩
  · rintro ⟨p, q, rfl, rfl, hpq⟩
    exact ⟨p, q, rfl, rfl,
      (starTriangle_reach_iff E A B C O ωt ωs hAB hAC hBC hOA hOB hOC hm hEO hu hv).2 hpq⟩

end Universality
end StatMech
