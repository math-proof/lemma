/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc47trifarms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc46funnelproof.Part6
import Def.StatisticalMechanics.Code.Walls.bc47trifarms.Part4
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc47_removeSite_le (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSite x ω ≤ ω := by
  rw [← daep_removeSites_singleton x ω]
  exact daep_removeSites_le {x} ω


theorem bc47_isTrifurcation_of_classical (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (h : bc47_IsClassicalTrifurcation ω x) : IsTrifurcation d ω x := by
  obtain ⟨a₁, a₂, a₃, hne, ⟨he1, he2, he3⟩, ⟨hi1, hi2, hi3⟩, hsep⟩ := h
  refine ⟨a₁, a₂, a₃, hne, ⟨he1.connected, he2.connected, he3.connected⟩, ?_, hsep⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hi1.mono (cluster_mono (bc47_removeSite_le x ω) a₁)
  · exact hi2.mono (cluster_mono (bc47_removeSite_le x ω) a₂)
  · exact hi3.mono (cluster_mono (bc47_removeSite_le x ω) a₃)


theorem bc47_only_infinite_neighbour_is_R1 (a : Site 2)
    (hea : IsOpenEdge 2 bc47_fakeConfig bc47_x a)
    (hia : (cluster 2 (removeSite bc47_x bc47_fakeConfig) a).Infinite) : a = bc47_R 1 := by
  by_contra hne
  
  
  have hxa_ne : a ≠ bc47_x := (hea.1.ne).symm
  have hopen := hea.2
  rw [bc47_fakeConfig] at hopen
  by_cases hstub : (∃ i : Fin 3, s(bc47_x, a) = bc47_armEdge i)
  · obtain ⟨i, hi⟩ := hstub
    
    
    have harm : a = bc47_a1 ∨ a = bc47_a2 ∨ a = bc47_a3 := by
      have hedge : s(bc47_x, a) = s(bc47_x, bc47_a1) ∨ s(bc47_x, a) = s(bc47_x, bc47_a2) ∨
          s(bc47_x, a) = s(bc47_x, bc47_a3) := by
        fin_cases i
        · exact Or.inl (hi.trans bc47_armEdge_zero)
        · exact Or.inr (Or.inl (hi.trans bc47_armEdge_one))
        · exact Or.inr (Or.inr (hi.trans bc47_armEdge_two))
      rcases hedge with he | he | he <;>
        · rw [Sym2.eq_iff] at he
          rcases he with ⟨_, ha⟩ | ⟨_, hax⟩
          · first | (exact Or.inl ha) | (exact Or.inr (Or.inl ha))
                  | (exact Or.inr (Or.inr ha))
          · exact absurd hax hxa_ne
    exact absurd (bc47_arm_removeSite_finite a harm) hia
  · rw [if_neg hstub] at hopen
    by_cases hray : (∃ k : ℤ, 0 ≤ k ∧ s(bc47_x, a) = s(bc47_R k, bc47_R (k + 1)))
    · obtain ⟨k, hk, hek⟩ := hray
      rw [bc47_x_eq_R0, Sym2.eq_iff] at hek
      rcases hek with ⟨hx, ha⟩ | ⟨hx, ha⟩
      · 
        have hk0 : (0 : ℤ) = k := bc47_R_inj hx
        rw [← hk0] at ha
        exact hne (ha.trans (by norm_num))
      · 
        have : (0 : ℤ) = k + 1 := bc47_R_inj hx
        omega
    · rw [if_neg hray] at hopen; exact Bool.false_ne_true hopen


theorem bc47_not_classical_fakeConfig :
    ¬ bc47_IsClassicalTrifurcation bc47_fakeConfig bc47_x := by
  rintro ⟨a₁, a₂, a₃, ⟨h12, _, _⟩, ⟨he1, he2, _⟩, ⟨hi1, hi2, _⟩, _⟩
  have e1 := bc47_only_infinite_neighbour_is_R1 a₁ he1 hi1
  have e2 := bc47_only_infinite_neighbour_is_R1 a₂ he2 hi2
  exact h12 (e1.trans e2.symm)


theorem arc_trifArmsRemoveSiteInfinite_of_classical (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcl : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc47_IsClassicalTrifurcation ω x) :
    arc_TrifArmsRemoveSiteInfinite ω n := by
  intro x hxbox htri
  obtain ⟨a₁, a₂, a₃, hne, ⟨he1, he2, he3⟩, hinf, hsep⟩ := hcl x hxbox htri
  
  refine ⟨![a₁, a₂, a₃], ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact ⟨he1.1, he1.2⟩
    · exact ⟨he2.1, he2.2⟩
    · exact ⟨he3.1, he3.2⟩
  · 
    intro i; fin_cases i
    · exact (he1.1.ne).symm
    · exact (he2.1.ne).symm
    · exact (he3.1.ne).symm
  · exact hsep
  · intro i; fin_cases i
    · exact hinf.1
    · exact hinf.2.1
    · exact hinf.2.2


theorem bc47_trif_arm_data_of_classical (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcl : ∀ x, x ∈ box d n → IsTrifurcation d ω x → bc47_IsClassicalTrifurcation ω x)
    (x : Site d) (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d),
      (∀ i, (openSubgraph d ω).Adj x (c i)) ∧
      (∀ i, c i ≠ x) ∧
      (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
       ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
       ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧
      (∀ i, zr i ∈ vertexBoundary d (n + 1) ∧
        ∃ w : (openSubgraph d (removeSite x ω)).Walk (c i) (zr i), x ∉ w.support) :=
  arc_trif_arm_data ω n (arc_trifArmsRemoveSiteInfinite_of_classical ω n hcl) x hxbox htri


end StatMech.Walls
