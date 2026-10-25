/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc30armforest.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKArmSelectorClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc28forestroot.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc29armdiv.Part3
import Def.StatisticalMechanics.Code.Walls.bc30armforest.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc30_globalCutDownArmData_of_upArmFunneling (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (h : bc30_UpArmFunneling ω n rank) :
    bc30_GlobalCutDownArmData ω n rank := by
  obtain ⟨b, u, hbdata, hdown, hfun⟩ := h
  refine ⟨b, hbdata, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  
  have hfunxy : Connected d (removeSite y ω) (b x) (u y) :=
    hfun x hxbox htri y hybox htriy hxy hconn hlt
  
  have hdowny : ¬ Connected d (removeSite y ω) (b y) (u y) := hdown y hybox htriy
  
  intro hbybx
  exact hdowny (hbybx.trans hfunxy)


theorem bc30_bundledRootedDownArmForest_of_upArmFunneling (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (rank : Site d → ℕ ×ₗ ℕ)
    (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y)
    (h : bc30_UpArmFunneling ω n rank) :
    bc29_BundledRootedDownArmForest ω n :=
  bc30_bundledRootedDownArmForest_of_data ω n rank hinj
    (bc30_globalCutDownArmData_of_upArmFunneling ω n rank h)


theorem bc30_upArmFunneling_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n)
    (hydata : ∀ i, y i ∈ box d n ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby : ∀ i, b (y i) ∈ box d n ∧ Connected d ω (y i) (b (y i)) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b (y i))).Infinite)
    
    (hx0down : ¬ Connected d (removeSite x₀ ω) (b x₀) x₀)
    
    
    
    (hsx0 : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) (b x₀))
    
    
    
    
    
    (hsibfun : ∀ i j : Fin 3, (j : ℕ) < i →
      Connected d (removeSite (y i) ω) (b (y j)) (b x₀)) :
    bc30_UpArmFunneling ω n
      (fun z => if z = x₀ then toLex (0, 0)
                else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0)) := by
  classical
  set rank : Site d → ℕ ×ₗ ℕ := fun z =>
    if z = x₀ then toLex (0, 0)
    else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0) with hrank
  have hrx0 : rank x₀ = toLex (0, 0) := by simp only [hrank, if_pos rfl]
  have hry : ∀ i, rank (y i) = toLex (1, (i : ℕ)) := by
    intro i
    have hne : y i ≠ x₀ := (hydata i).2.1.symm
    have hex : ∃ k, y i = y k := ⟨i, rfl⟩
    have hchoose : hex.choose = i := hyinj hex.choose_spec.symm
    simp only [hrank, if_neg hne, dif_pos hex, hchoose]
  
  refine ⟨b, (fun z => if z = x₀ then x₀ else b x₀), ?_, ?_, ?_⟩
  · 
    intro x hxbox htri
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩
    · exact hbx0
    · exact hby i
  · 
    intro yv hyvbox htriv
    rcases hsingle yv hyvbox htriv with rfl | ⟨i, rfl⟩
    · 
      simpa using hx0down
    · 
      have hne : y i ≠ x₀ := (hydata i).2.1.symm
      simp only [if_neg hne]; exact hsx0 i
  · 
    intro x hxbox htri yv hyvbox htriv hxy hconn hlt
    rcases hsingle yv hyvbox htriv with rfl | ⟨i, rfl⟩
    · 
      rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
      · exact absurd rfl hxy
      · rw [hry j, hrx0] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · 
      have hne : y i ≠ x₀ := (hydata i).2.1.symm
      simp only [if_neg hne]
      rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
      · 
        
        
        exact connected_rfl
      · 
        
        rw [hry j, hry i] at hlt
        have hji : (j : ℕ) < i := by
          rw [Prod.Lex.toLex_lt_toLex] at hlt
          rcases hlt with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl 1)
          · exact h
        exact hsibfun i j hji


theorem bc30_upArmFunneling_clauses_consistent :
    ∃ (ω : ConfigSpace (Sym2 (Site 1))) (y by' uy bx₁ bx₂ : Site 1),
      ¬ Connected 1 (removeSite y ω) by' uy ∧          
      Connected 1 (removeSite y ω) bx₁ uy ∧            
      ¬ Connected 1 (removeSite y ω) by' bx₂ ∧         
      Connected 1 (removeSite y ω) bx₂ uy := by        
  refine ⟨rfp_ωpath, rfp_p1, rfp_p2, rfp_p0, rfp_p0, rfp_p0, ?_, ?_, ?_, ?_⟩
  · 
    exact fun h => rfp_consistency_crossed h
  · 
    exact connected_rfl
  · 
    exact fun h => rfp_consistency_crossed h
  · 
    exact connected_rfl


theorem bc30_upArmFunneling_of_threeChain (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g : Site d} (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n) (hmbox : m ∈ box d n) (hgbox : g ∈ box d n)
    (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hmg : m ≠ g)
    (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b m)).Infinite)
    (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b g)).Infinite)
    
    (hx0down : ¬ Connected d (removeSite x₀ ω) (b x₀) x₀)
    (hmdown : ¬ Connected d (removeSite m ω) (b m) (b x₀))
    (hgdown : ¬ Connected d (removeSite g ω) (b g) (b m))
    
    (hfunx0g : Connected d (removeSite g ω) (b x₀) (b m)) :
    bc30_UpArmFunneling ω n
      (fun z => if z = x₀ then toLex (0, 0)
                else if z = m then toLex (1, 0) else toLex (2, 0)) := by
  classical
  set dep : Site d → ℕ := fun z => if z = x₀ then 0 else if z = m then 1 else 2 with hdep
  have hdepx0 : dep x₀ = 0 := by simp [hdep]
  have hdepm : dep m = 1 := by simp [hdep, hx0m.symm]
  have hdepg : dep g = 2 := by simp [hdep, hx0g.symm, hmg.symm]
  have hrankeq : (fun z : Site d => if z = x₀ then toLex (0, 0)
        else if z = m then toLex (1, 0) else toLex (2, 0))
      = fun z => toLex (dep z, 0) := by
    funext z; simp only [hdep]; split_ifs <;> rfl
  rw [hrankeq]
  
  refine ⟨b, (fun z => if z = x₀ then x₀ else if z = m then b x₀ else b m), ?_, ?_, ?_⟩
  · 
    intro x hxbox htri
    rcases hthree x hxbox htri with rfl | rfl | rfl
    · exact hbx0
    · exact hbm
    · exact hbg
  · 
    intro yv hyvbox htriv
    rcases hthree yv hyvbox htriv with rfl | rfl | rfl
    · simpa using hx0down
    · simp only [if_neg hx0m.symm]; exact hmdown
    · simp only [if_neg hx0g.symm, if_neg hmg.symm]; exact hgdown
  · 
    intro x hxbox htri yv hyvbox htriv hxy hconn hlt
    rcases hthree yv hyvbox htriv with rfl | rfl | rfl
    · 
      rcases hthree x hxbox htri with rfl | rfl | rfl
      · exact absurd rfl hxy
      · simp only [] at hlt; rw [hdepm, hdepx0] at hlt
        exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · simp only [] at hlt; rw [hdepg, hdepx0] at hlt
        exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · 
      simp only [if_neg hx0m.symm]
      rcases hthree x hxbox htri with rfl | rfl | rfl
      · exact connected_rfl
      · exact absurd rfl hxy
      · simp only [] at hlt; rw [hdepg, hdepm] at hlt
        exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · 
      simp only [if_neg hx0g.symm, if_neg hmg.symm]
      rcases hthree x hxbox htri with rfl | rfl | rfl
      · exact hfunx0g
      · exact connected_rfl
      · exact absurd rfl hxy

end StatMech.Walls
