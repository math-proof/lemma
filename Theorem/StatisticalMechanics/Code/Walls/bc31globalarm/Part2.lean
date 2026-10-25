/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc31globalarm.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc29armdiv.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc30armforest.Part2
import Def.StatisticalMechanics.Code.Walls.bc31globalarm
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc31_globalCutDownArmData_of_TfreeDownArmData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (h : bc31_TfreeDownArmData ω n rank) :
    bc30_GlobalCutDownArmData ω n rank := by
  obtain ⟨b, hbdata, hsplit⟩ := h
  rw [bc30_globalCutDownArmData_iff_rootedDownArmForest]
  refine ⟨b, ?_, hsplit⟩
  intro x hxbox htri
  obtain ⟨hbbox, hbconn, hbinf, hbTfree⟩ := hbdata x hxbox htri
  exact ⟨hbbox, hbconn, bc31_globalCut_infinite_of_singleCut_Tfree ω hbinf hbTfree⟩


theorem bc31_bundledRootedDownArmForest_of_TfreeDownArmData (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (rank : Site d → ℕ ×ₗ ℕ)
    (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y)
    (h : bc31_TfreeDownArmData ω n rank) :
    bc29_BundledRootedDownArmForest ω n :=
  bc30_bundledRootedDownArmForest_of_data ω n rank hinj
    (bc31_globalCutDownArmData_of_TfreeDownArmData ω n rank h)


theorem bc31_Tcount_le_boundary_of_TfreeDownArmData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (rank : Site d → ℕ ×ₗ ℕ)
    (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x ≠ rank y)
    (h : bc31_TfreeDownArmData ω n rank) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc30_Tcount_le_boundary_of_data ω n hn rank hinj
    (bc31_globalCutDownArmData_of_TfreeDownArmData ω n rank h)


theorem bc31_removeSite_notConnected_self {x a : Site d} (ω : ConfigSpace (Sym2 (Site d)))
    (hax : a ≠ x) : ¬ Connected d (removeSite x ω) a x := by
  intro h
  obtain ⟨w⟩ := h
  exact arc_walk_avoids_x hax w (by simp)


theorem bc31_globalCutDownArmData_of_uniqueTrif_singleCut
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (rank : Site d → ℕ ×ₗ ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a) (hax0 : a ≠ x₀)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    bc30_GlobalCutDownArmData ω n rank := by
  apply bc31_globalCutDownArmData_of_TfreeDownArmData
  refine ⟨fun _ => a, ?_, ?_⟩
  · intro x hxbox htri
    obtain rfl := huniq x hxbox htri
    refine ⟨habox, haconn, hainf, ?_⟩
    intro z hz hzT
    rw [tfc_mem_trifFinset] at hzT
    have hzx0 : z = x := huniq z hzT.1 hzT.2
    rw [hzx0] at hz
    exact bc31_removeSite_notConnected_self ω hax0 hz
  · intro x hxbox htri y hybox htriy hxy _ _
    have h1 := huniq x hxbox htri
    have h2 := huniq y hybox htriy
    exact absurd (h1.trans h2.symm) hxy


theorem bc31_TfreeDownArmData_clauses_consistent :
    ∃ (ω : ConfigSpace (Sym2 (Site 1))) (y bx by' : Site 1),
      (∀ z, Connected 1 (removeSite y ω) by' z → z ≠ y ∧ z ≠ bx) ∧
      ¬ Connected 1 (removeSite y ω) by' bx := by
  refine ⟨rfp_ωpath, rfp_p1, rfp_p0, rfp_p2, ?_, ?_⟩
  · intro z hz
    have heq := rfp_path_conn_eq_after_p1 hz
    subst heq
    refine ⟨?_, ?_⟩
    · intro h; have := congrFun h ⟨0, by norm_num⟩; simp [rfp_p2, rfp_p1] at this
    · intro h; have := congrFun h ⟨0, by norm_num⟩; simp [rfp_p2, rfp_p0] at this
  · intro h
    have heq := rfp_path_conn_eq_after_p1 h
    have := congrFun heq ⟨0, by norm_num⟩; simp [rfp_p2, rfp_p0] at this


theorem bc31_TfreeDownArmData_of_threeChain (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g : Site d} (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n) (hmbox : m ∈ box d n) (hgbox : g ∈ box d n)
    (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hmg : m ≠ g)
    (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSite x₀ ω) (b x₀)).Infinite ∧
      (∀ z, Connected d (removeSite x₀ ω) (b x₀) z → z ≠ x₀ ∧ z ≠ m ∧ z ≠ g))
    (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧
      (cluster d (removeSite m ω) (b m)).Infinite ∧
      (∀ z, Connected d (removeSite m ω) (b m) z → z ≠ x₀ ∧ z ≠ m ∧ z ≠ g))
    (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧
      (cluster d (removeSite g ω) (b g)).Infinite ∧
      (∀ z, Connected d (removeSite g ω) (b g) z → z ≠ x₀ ∧ z ≠ m ∧ z ≠ g))
    (hsxm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
    (hsxg : ¬ Connected d (removeSite g ω) (b g) (b x₀))
    (hsmg : ¬ Connected d (removeSite g ω) (b g) (b m)) :
    bc31_TfreeDownArmData ω n
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
  rw [show (fun z : Site d => if z = x₀ then toLex (0, 0)
        else if z = m then toLex (1, 0) else toLex (2, 0))
      = fun z => toLex (dep z, 0) from hrankeq]
  refine ⟨b, ?_, ?_⟩
  · 
    have hTfree : ∀ {a : Site d},
        (∀ z, Connected d (removeSite a ω) (b a) z → z ≠ x₀ ∧ z ≠ m ∧ z ≠ g) →
        (∀ z, Connected d (removeSite a ω) (b a) z → z ∉ tfc_trifFinset ω n) := by
      intro a hne z hz hzT
      rw [tfc_mem_trifFinset] at hzT
      rcases hthree z hzT.1 hzT.2 with rfl | rfl | rfl
      · exact (hne z hz).1 rfl
      · exact (hne z hz).2.1 rfl
      · exact (hne z hz).2.2 rfl
    intro x hxbox htri
    rcases hthree x hxbox htri with rfl | rfl | rfl
    · exact ⟨hbx0.1, hbx0.2.1, hbx0.2.2.1, hTfree hbx0.2.2.2⟩
    · exact ⟨hbm.1, hbm.2.1, hbm.2.2.1, hTfree hbm.2.2.2⟩
    · exact ⟨hbg.1, hbg.2.1, hbg.2.2.1, hTfree hbg.2.2.2⟩
  · intro x hxbox htri y hybox htriy hxy _ hlt
    rcases hthree x hxbox htri with rfl | rfl | rfl <;>
      rcases hthree y hybox htriy with rfl | rfl | rfl
    · exact absurd rfl hxy
    · exact hsxm
    · exact hsxg
    · simp only [] at hlt; rw [hdepm, hdepx0] at hlt
      exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · exact absurd rfl hxy
    · exact hsmg
    · simp only [] at hlt; rw [hdepg, hdepx0] at hlt
      exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · simp only [] at hlt; rw [hdepg, hdepm] at hlt
      exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · exact absurd rfl hxy


theorem bc31_TfreeDownArmData_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n)
    (hydata : ∀ i, y i ∈ box d n ∧ x₀ ≠ y i ∧ Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSite x₀ ω) (b x₀)).Infinite ∧
      (∀ z, Connected d (removeSite x₀ ω) (b x₀) z → z ≠ x₀ ∧ ∀ i, z ≠ y i))
    (hby : ∀ i, b (y i) ∈ box d n ∧ Connected d ω (y i) (b (y i)) ∧
      (cluster d (removeSite (y i) ω) (b (y i))).Infinite ∧
      (∀ z, Connected d (removeSite (y i) ω) (b (y i)) z → z ≠ x₀ ∧ ∀ j, z ≠ y j))
    (hsx0 : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) (b x₀))
    (hssib : ∀ i j : Fin 3, (j : ℕ) < i →
      ¬ Connected d (removeSite (y i) ω) (b (y i)) (b (y j))) :
    bc31_TfreeDownArmData ω n
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
  
  have hTfree : ∀ {a : Site d},
      (∀ z, Connected d (removeSite a ω) (b a) z → z ≠ x₀ ∧ ∀ i, z ≠ y i) →
      (∀ z, Connected d (removeSite a ω) (b a) z → z ∉ tfc_trifFinset ω n) := by
    intro a hne z hz hzT
    rw [tfc_mem_trifFinset] at hzT
    have hnez := hne z hz
    rcases hsingle z hzT.1 hzT.2 with rfl | ⟨i, rfl⟩
    · exact hnez.1 rfl
    · exact hnez.2 i rfl
  refine ⟨b, ?_, ?_⟩
  · 
    intro x hxbox htri
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩
    · exact ⟨hbx0.1, hbx0.2.1, hbx0.2.2.1, hTfree hbx0.2.2.2⟩
    · exact ⟨(hby i).1, (hby i).2.1, (hby i).2.2.1, hTfree (hby i).2.2.2⟩
  · 
    intro x hxbox htri yv hyvbox htriv hxy hconn hlt
    rcases hsingle yv hyvbox htriv with rfl | ⟨i, rfl⟩
    · rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
      · exact absurd rfl hxy
      · rw [hry j, hrx0] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
      · exact hsx0 i
      · rw [hry j, hry i] at hlt
        have hji : (j : ℕ) < i := by
          rw [Prod.Lex.toLex_lt_toLex] at hlt
          rcases hlt with h | ⟨_, h⟩
          · exact absurd h (lt_irrefl 1)
          · exact h
        exact hssib i j hji

end StatMech.Walls
