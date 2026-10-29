/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc35globalarm
import Theorem.StatisticalMechanics.Code.Walls.bc36rooteddiv.Part2
import Def.StatisticalMechanics.Code.Walls.bc37armadj.Part5
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


set_option linter.style.longLine false


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc37_downArmSelector_of_parentFunneling (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc37_ParentFunneling ω n) : bc37_DownArmSelector ω n := by
  obtain ⟨b, rank, par, hdata, hrank, hpar⟩ := h
  refine ⟨b, rank, hdata, hrank, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hlocal, hself, hfunnel⟩ := hpar x hxbox htri y hybox htriy hxy hconn hlt
  by_cases hxpar : x = par y
  · 
    rw [hxpar]; exact hlocal
  · 
    intro hconn_by_bx
    exact hself (hconn_by_bx.trans (hfunnel hxpar))


theorem bc37_selfDownArm_of_parentFunneling (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc37_ParentFunneling ω n) : bc36_SelfDownArm ω n :=
  bc37_selfDownArm_of_downArmSelector ω n (bc37_downArmSelector_of_parentFunneling ω n h)


theorem bc37_armForestRooting_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc37_ArmForestRooting ω n := by
  refine ⟨id, (fun _ => toLex (0, 0)), id, ?_, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)


theorem bc37_armForestRooting_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hdiv : ¬ Connected d (removeSite y₀ ω) (b y₀) (b x₀)) :
    bc37_ArmForestRooting ω n := by
  classical
  apply bc37_armForestRooting_of_downArmSelector
  refine ⟨b, (fun z => if z = y₀ then toLex (1, 0) else toLex (0, 0)), ?_, ?_, ?_⟩
  · intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hbx0
    · exact hby0
  · intro x hxbox htri y hybox htriy hxy _
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · simp only [if_neg hx0y0, if_pos]; exact stt_lex_ne_fst (by norm_num)
    · rcases htwo y hybox htriy with rfl | rfl
      · simp only [if_neg hx0y0, if_pos]; exact stt_lex_ne_fst (by norm_num)
      · exact absurd rfl hxy
  · intro x hxbox htri y hybox htriy hxy _ hlt
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · exact hdiv
    · rcases htwo y hybox htriy with rfl | rfl
      · simp only [if_neg hx0y0, if_pos] at hlt
        exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · exact absurd rfl hxy

set_option linter.unusedSimpArgs false in


theorem bc37_armForestRooting_of_threeChain (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g : Site d} (b : Site d → Site d)
    (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hmg : m ≠ g)
    (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b m)).Infinite)
    (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b g)).Infinite)
    (hsxm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
    (hsxg : ¬ Connected d (removeSite g ω) (b g) (b x₀))
    (hsmg : ¬ Connected d (removeSite g ω) (b g) (b m)) :
    bc37_ArmForestRooting ω n := by
  classical
  apply bc37_armForestRooting_of_downArmSelector
  refine ⟨b, (fun z => if z = x₀ then toLex (0, 0)
              else if z = m then toLex (1, 0) else toLex (2, 0)), ?_, ?_, ?_⟩
  · intro x hxbox htri
    rcases hthree x hxbox htri with rfl | rfl | rfl
    · exact hbx0
    · exact hbm
    · exact hbg
  · intro x hxbox htri y hybox htriy hxy _
    simp only
    rcases hthree x hxbox htri with rfl | rfl | rfl <;>
      rcases hthree y hybox htriy with rfl | rfl | rfl <;>
      simp only [↓reduceIte, if_neg hx0m.symm, if_neg hx0g.symm, if_neg hmg.symm,
        if_neg hx0m, if_neg hx0g, if_neg hmg] <;>
      first
      | exact absurd rfl hxy
      | exact stt_lex_ne_fst (by norm_num)
  · intro x hxbox htri y hybox htriy hxy _ hlt
    simp only at hlt
    rcases hthree y hybox htriy with rfl | rfl | rfl <;>
      rcases hthree x hxbox htri with rfl | rfl | rfl <;>
      simp only [↓reduceIte, if_neg hx0m, if_neg hx0g, if_neg hmg,
        if_neg hx0m.symm, if_neg hx0g.symm, if_neg hmg.symm] at hlt ⊢ <;>
      first
      | exact absurd rfl hxy
      | exact hsxm
      | exact hsxg
      | exact hsmg
      | exact absurd hlt (stt_lex_not_lt_fst (by norm_num))


theorem bc37_armForestRooting_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (lx : Site d → Fin 3) (ly : Fin 3 → Site d → Fin 3)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v →
      (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
    (hGstar : ∀ i w, Connected d ω x₀ w → x₀ ≠ w → Connected d ω (y i) w → y i ≠ w →
      (ly i w = 0 ↔ lx w ≠ i))
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
    (b : Site d → Site d)
    (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hcy : ∀ i, lx (b (y i)) = i)
    {j₀ : Fin 3} (hcx : lx (b x₀) = j₀)
    (hcentral : ly j₀ (b x₀) ≠ ly j₀ (b (y j₀))) :
    bc37_ArmForestRooting ω n :=
  bc37_armForestRooting_of_singleCutSep ω n
    (fcc_rootedSingleCutSeparation_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar
      hsingle b hbdata hcy hcx hcentral)

set_option linter.unusedSimpArgs false in


theorem bc37_armForestRooting_of_fourTree (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g h : Site d} (b : Site d → Site d)
    (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hx0h : x₀ ≠ h) (hmg : m ≠ g) (hmh : m ≠ h) (hgh : g ≠ h)
    (hfour : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g ∨ x = h)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b m)).Infinite)
    (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b g)).Infinite)
    (hbh : b h ∈ box d n ∧ Connected d ω h (b h) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b h)).Infinite)
    
    (hm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
    (hg_x0 : ¬ Connected d (removeSite g ω) (b g) (b x₀))
    (hg_m : ¬ Connected d (removeSite g ω) (b g) (b m))
    (hh_x0 : ¬ Connected d (removeSite h ω) (b h) (b x₀))
    (hh_m : ¬ Connected d (removeSite h ω) (b h) (b m))
    (hh_g : ¬ Connected d (removeSite h ω) (b h) (b g)) :
    bc37_ArmForestRooting ω n := by
  classical
  apply bc37_armForestRooting_of_downArmSelector
  refine ⟨b, (fun z => if z = x₀ then toLex (0, 0) else if z = m then toLex (1, 0)
              else if z = g then toLex (2, 0) else toLex (3, 0)), ?_, ?_, ?_⟩
  · intro x hxbox htri
    rcases hfour x hxbox htri with rfl | rfl | rfl | rfl
    · exact hbx0
    · exact hbm
    · exact hbg
    · exact hbh
  · intro x hxbox htri y hybox htriy hxy _
    simp only
    rcases hfour x hxbox htri with rfl | rfl | rfl | rfl <;>
      rcases hfour y hybox htriy with rfl | rfl | rfl | rfl <;>
      simp only [↓reduceIte, if_neg hx0m.symm, if_neg hx0g.symm, if_neg hx0h.symm,
        if_neg hmg.symm, if_neg hmh.symm, if_neg hgh.symm] <;>
      first
      | exact absurd rfl hxy
      | exact stt_lex_ne_fst (by norm_num)
  · intro x hxbox htri y hybox htriy hxy _ hlt
    simp only at hlt
    rcases hfour y hybox htriy with rfl | rfl | rfl | rfl <;>
      rcases hfour x hxbox htri with rfl | rfl | rfl | rfl <;>
      simp only [↓reduceIte, if_neg hx0m, if_neg hx0g, if_neg hx0h, if_neg hmg, if_neg hmh,
        if_neg hgh, if_neg hx0m.symm, if_neg hx0g.symm, if_neg hx0h.symm, if_neg hmg.symm,
        if_neg hmh.symm, if_neg hgh.symm] at hlt <;>
      first
      | exact absurd rfl hxy
      | exact hm
      | exact hg_x0
      | exact hg_m
      | exact hh_x0
      | exact hh_m
      | exact hh_g
      | exact absurd hlt (stt_lex_not_lt_fst (by norm_num))


theorem bc37_Tcount_le_boundary_of_armForestRooting (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : bc37_ArmForestRooting ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc36_Tcount_le_boundary_of_selfDownArm ω n hn (bc37_selfDownArm_of_armForestRooting ω n h)


theorem bc37_burton_keane_bernoulli_of_armForestRooting (hd : 1 ≤ d) (p : NNReal)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc37_ArmForestRooting ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc36_burton_keane_bernoulli_of_selfDownArm hd p hp1 hp0
    (fun ω n hn => bc37_selfDownArm_of_armForestRooting ω n (hres ω n hn)) htrif


theorem bc37_parentFunneling_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc37_ParentFunneling ω n := by
  refine ⟨id, (fun _ => toLex (0, 0)), id, ?_, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)


theorem bc37_parentFunneling_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hlocal : ¬ Connected d (removeSite y₀ ω) (b y₀) (b x₀))
    (hself : ¬ Connected d (removeSite y₀ ω) (b y₀) x₀) :
    bc37_ParentFunneling ω n := by
  classical
  refine ⟨b, (fun z => if z = y₀ then toLex (1, 0) else toLex (0, 0)),
    (fun _ => x₀), ?_, ?_, ?_⟩
  · intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hbx0
    · exact hby0
  · intro x hxbox htri y hybox htriy hxy _
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · simp only [if_neg hx0y0, if_pos]; exact stt_lex_ne_fst (by norm_num)
    · rcases htwo y hybox htriy with rfl | rfl
      · simp only [if_neg hx0y0, if_pos]; exact stt_lex_ne_fst (by norm_num)
      · exact absurd rfl hxy
  · intro x hxbox htri y hybox htriy hxy _ hlt
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo y hybox htriy with rfl | rfl
      · exact absurd rfl hxy
      · exact ⟨hlocal, hself, fun hne => absurd rfl hne⟩
    · rcases htwo y hybox htriy with rfl | rfl
      · simp only [if_neg hx0y0, if_pos] at hlt
        exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · exact absurd rfl hxy


theorem bc37_parentFunneling_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby : ∀ i, b (y i) ∈ box d n ∧ Connected d ω (y i) (b (y i)) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b (y i))).Infinite)
    (hloc : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) (b x₀))
    (hself : ∀ i, ¬ Connected d (removeSite (y i) ω) (b (y i)) x₀)
    (hfun : ∀ i j : Fin 3, (j : ℕ) < i →
      Connected d (removeSite (y i) ω) (b (y j)) x₀) :
    bc37_ParentFunneling ω n := by
  classical
  set rank : Site d → ℕ ×ₗ ℕ := fun z =>
    if z = x₀ then toLex (0, 0)
    else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0) with hrank
  have hrx0 : rank x₀ = toLex (0, 0) := by simp only [hrank, if_pos rfl]
  have hry : ∀ i, rank (y i) = toLex (1, (i : ℕ)) := by
    intro i
    have hne : y i ≠ x₀ := (hydata i).2.2.1.symm
    have hex : ∃ k, y i = y k := ⟨i, rfl⟩
    have hchoose : hex.choose = i := hyinj hex.choose_spec.symm
    simp only [hrank, if_neg hne, dif_pos hex, hchoose]
  refine ⟨b, rank, (fun _ => x₀), ?_, ?_, ?_⟩
  · 
    intro x hxbox htri
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩
    · exact hbx0
    · exact hby i
  · 
    intro x hxbox htri yv hyvbox htriv hxy _
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩ <;>
      rcases hsingle yv hyvbox htriv with rfl | ⟨j, rfl⟩
    · exact absurd rfl hxy
    · rw [hrx0, hry j]; exact stt_lex_ne_fst (by norm_num)
    · rw [hrx0, hry i]; exact (stt_lex_ne_fst (by norm_num)).symm
    · rw [hry i, hry j]
      have hij : i ≠ j := fun h => hxy (congrArg y h)
      exact stt_lex_ne_snd (fun he => hij (Fin.ext he))
  · 
    intro x hxbox htri yv hyvbox htriv hxy hconn hlt
    rcases hsingle yv hyvbox htriv with rfl | ⟨i, rfl⟩
    · 
      rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
      · exact absurd rfl hxy
      · rw [hry j, hrx0] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · 
      refine ⟨hloc i, hself i, ?_⟩
      intro hxne
      rcases hsingle x hxbox htri with rfl | ⟨j, rfl⟩
      · 
        exact absurd rfl hxne
      · 
        rw [hry j, hry i] at hlt
        have hji : (j : ℕ) < i := by
          rw [Prod.Lex.toLex_lt_toLex] at hlt
          rcases hlt with hh | ⟨_, hh⟩
          · exact absurd hh (lt_irrefl 1)
          · exact hh
        exact hfun i j hji


theorem bc37_claw_funnelShadow_consistent (x0node bx0 : ℕ) (byv : Fin 3 → ℕ) (i : Fin 3)
    (hnode : x0node ≠ byv i) (hdistinct : ∀ j, byv j ≠ bx0) (hbyinj : Function.Injective byv) :
    ∃ up : ℕ → Prop,
      (¬ up (byv i) ∧ up bx0) ∧          
      (¬ up (byv i) ∧ up x0node) ∧       
      (∀ j, j ≠ i → up x0node ∧ up (byv j)) := by  
  refine ⟨fun w => w ≠ byv i, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · simp                                 
  · exact (hdistinct i).symm             
  · simp                                 
  · exact hnode                          
  · intro j hji
    refine ⟨hnode, ?_⟩                   
    exact fun he => hji (hbyinj he)      

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in


theorem bc37_parentFunneling_of_threeChain (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g : Site d} (b : Site d → Site d)
    (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hmg : m ≠ g)
    (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hbm : b m ∈ box d n ∧ Connected d ω m (b m) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b m)).Infinite)
    (hbg : b g ∈ box d n ∧ Connected d ω g (b g) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b g)).Infinite)
    (hlm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
    (hsm : ¬ Connected d (removeSite m ω) (b m) x₀)
    (hlg : ¬ Connected d (removeSite g ω) (b g) (b m))
    (hsg : ¬ Connected d (removeSite g ω) (b g) m)
    (hfg : Connected d (removeSite g ω) (b x₀) m) :
    bc37_ParentFunneling ω n := by
  classical
  set dep : Site d → ℕ := fun z => if z = x₀ then 0 else if z = m then 1 else 2 with hdep
  have hdx0 : dep x₀ = 0 := by simp [hdep]
  have hdm : dep m = 1 := by simp [hdep, hx0m.symm]
  have hdg : dep g = 2 := by simp [hdep, hx0g.symm, hmg.symm]
  refine ⟨b, (fun z => toLex (dep z, 0)), (fun z => if z = g then m else x₀), ?_, ?_, ?_⟩
  · intro x hxbox htri
    rcases hthree x hxbox htri with rfl | rfl | rfl
    · exact hbx0
    · exact hbm
    · exact hbg
  · intro x hxbox htri yv hyvbox htriv hxy _
    simp only
    rcases hthree x hxbox htri with rfl | rfl | rfl <;>
      rcases hthree yv hyvbox htriv with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hxy
      | (first
          | (rw [hdx0, hdm]; exact stt_lex_ne_fst (by norm_num))
          | (rw [hdx0, hdg]; exact stt_lex_ne_fst (by norm_num))
          | (rw [hdm, hdx0]; exact stt_lex_ne_fst (by norm_num))
          | (rw [hdm, hdg]; exact stt_lex_ne_fst (by norm_num))
          | (rw [hdg, hdx0]; exact stt_lex_ne_fst (by norm_num))
          | (rw [hdg, hdm]; exact stt_lex_ne_fst (by norm_num)))
  · intro x hxbox htri yv hyvbox htriv hxy _ hlt
    simp only at hlt
    rcases hthree yv hyvbox htriv with rfl | rfl | rfl
    · 
      rcases hthree x hxbox htri with rfl | rfl | rfl
      · exact absurd rfl hxy
      · rw [hdm, hdx0] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · rw [hdg, hdx0] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · 
      simp only [if_neg hmg]
      rcases hthree x hxbox htri with rfl | rfl | rfl
      · exact ⟨hlm, hsm, fun hne => absurd rfl hne⟩
      · exact absurd rfl hxy
      · rw [hdg, hdm] at hlt; exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
    · 
      simp only
      refine ⟨hlg, hsg, ?_⟩
      intro hxne
      rcases hthree x hxbox htri with rfl | rfl | rfl
      · 
        exact hfg
      · 
        exact absurd rfl hxne
      · exact absurd rfl hxy


theorem bc37_Tcount_le_boundary_of_parentFunneling (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : bc37_ParentFunneling ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bc36_Tcount_le_boundary_of_selfDownArm ω n hn (bc37_selfDownArm_of_parentFunneling ω n h)


theorem bc37_burton_keane_bernoulli_of_parentFunneling (hd : 1 ≤ d) (p : NNReal)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bc37_ParentFunneling ω n)
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc36_burton_keane_bernoulli_of_selfDownArm hd p hp1 hp0
    (fun ω n hn => bc37_selfDownArm_of_parentFunneling ω n (hres ω n hn)) htrif

end StatMech.Walls
