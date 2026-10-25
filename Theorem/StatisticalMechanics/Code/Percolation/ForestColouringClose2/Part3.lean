/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestColouringClose2.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsFinal.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BKHallSDRClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ForestAcyclicityClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.FacPairwiseClose
import Theorem.StatisticalMechanics.Code.Percolation.BKArmSelectorClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.RootedTreeSelectorClose
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
import Def.StatisticalMechanics.Code.Percolation.ForestColouringClose2.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem fcc_rootedSingleCutSeparation_of_rootedPrivateArm (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : fcc_RootedPrivateArm ω n) : fcc_RootedSingleCutSeparation ω n := by
  obtain ⟨b, rank, hbdata, hrank, hpair⟩ := h
  refine ⟨b, rank, hbdata, hrank, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  obtain ⟨hfar, hpriv⟩ := hpair x hxbox htri y hybox htriy hxy hconn hlt
  intro hbxby
  
  exact hpriv (hbxby.symm.trans hfar)


theorem fcc_rootedSpanningForest_of_armsPrivate (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcov : fcc_ThreeArmCover ω n) (hpriv : fcc_RootedPrivateArm ω n) :
    stt_RootedSpanningForest ω n :=
  fcc_rootedSpanningForest_of_coverSep ω n hcov
    (fcc_rootedSingleCutSeparation_of_rootedPrivateArm ω n hpriv)


theorem fcc_rootedSpanningForest_of_coverPrivate (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcov : fcc_ThreeArmCover ω n) (hpriv : fcc_RootedPrivateArm ω n) :
    stt_RootedSpanningForest ω n :=
  fcc_rootedSpanningForest_of_armsPrivate ω n hcov hpriv


theorem fcc_Tcount_le_boundary_of_armsPrivate (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hcov : fcc_ThreeArmCover ω n) (hpriv : fcc_RootedPrivateArm ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  stt_Tcount_le_boundary_of_rootedSpanningForest ω n hn
    (fcc_rootedSpanningForest_of_armsPrivate ω n hcov hpriv)


theorem fcc_burton_keane_bernoulli_of_armsPrivate (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hcov : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fcc_ThreeArmCover ω n)
    (hpriv : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → fcc_RootedPrivateArm ω n)
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
  stt_burton_keane_bernoulli_of_rootedSpanningForest hd p hp1 hp0
    (fun ω n hn => fcc_rootedSpanningForest_of_armsPrivate ω n (hcov ω n hn) (hpriv ω n hn))
    htrif


theorem fcc_threeArmCover_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    fcc_ThreeArmCover ω n := by
  refine ⟨fun _ _ => (0 : Site d), ?_⟩
  intro y hybox htriy; exact absurd htriy (hno y hybox)


theorem fcc_threeArmCover_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (lx : Site d → Fin 3) (ly : Fin 3 → Site d → Fin 3)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hlxf : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v →
      (lx u = lx v ↔ fsp_sameArm ω x₀ u v))
    (hlyf : ∀ i u v, Connected d ω (y i) u → y i ≠ u → Connected d ω (y i) v → y i ≠ v →
      (ly i u = ly i v ↔ fsp_sameArm ω (y i) u v))
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ ∃ i, x = y i) :
    fcc_ThreeArmCover ω n := by
  classical
  have hx0y : ∀ i, x₀ ≠ y i := fun i => (hydata i).2.2.1
  
  set c : Site d → Site d → Fin 3 :=
    fun z => if z = x₀ then lx
             else if h : ∃ i, z = y i then ly h.choose else lx with hc
  have hcyi : ∀ i, c (y i) = ly i := by
    intro i
    have hne : y i ≠ x₀ := (hx0y i).symm
    have hex : ∃ j, y i = y j := ⟨i, rfl⟩
    rw [hc]; simp only [if_neg hne, dif_pos hex]; rw [hyinj hex.choose_spec.symm]
  have hcx0 : c x₀ = lx := by simp [hc]
  refine fcc_threeArmCover_of_faithful ω n c ?_
  intro yy hyybox htriy u v hyu hneu hyv hnev
  rcases hsingle yy hyybox htriy with rfl | ⟨i, rfl⟩
  · rw [hcx0]; exact hlxf u v hyu hneu hyv hnev
  · rw [hcyi i]; exact hlyf i u v hyu hneu hyv hnev


theorem fcc_rootedPrivateArm_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    fcc_RootedPrivateArm ω n := by
  refine ⟨id, (fun _ => toLex (0, 0)), ?_, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)


theorem fcc_rootedPrivateArm_of_twoTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ : Site d} (b : Site d → Site d) (hx0y0 : x₀ ≠ y₀)
    (htwo : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = y₀)
    (hbx0 : b x₀ ∈ box d n ∧ Connected d ω x₀ (b x₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x₀)).Infinite)
    (hby0 : b y₀ ∈ box d n ∧ Connected d ω y₀ (b y₀) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b y₀)).Infinite)
    (hfar : Connected d (removeSite y₀ ω) (b x₀) x₀)
    (hpriv : ¬ Connected d (removeSite y₀ ω) (b y₀) x₀) :
    fcc_RootedPrivateArm ω n := by
  classical
  refine ⟨b, (fun z => if z = y₀ then toLex (1, 0) else toLex (0, 0)), ?_, ?_, ?_⟩
  · 
    intro x hxbox htri
    rcases htwo x hxbox htri with rfl | rfl
    · exact hbx0
    · exact hby0
  · 
    intro x hxbox htri x' hx'box htri' hxx' _
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo x' hx'box htri' with rfl | rfl
      · exact absurd rfl hxx'
      · simp only [if_neg hx0y0, if_pos]; exact stt_lex_ne_fst (by norm_num)
    · rcases htwo x' hx'box htri' with rfl | rfl
      · simp only [if_neg hx0y0, if_pos]; exact (stt_lex_ne_fst (by norm_num))
      · exact absurd rfl hxx'
  · 
    intro x hxbox htri x' hx'box htri' hxx' _ hlt
    rcases htwo x hxbox htri with rfl | rfl
    · rcases htwo x' hx'box htri' with rfl | rfl
      · exact absurd rfl hxx'
      · 
        exact ⟨hfar, hpriv⟩
    · rcases htwo x' hx'box htri' with rfl | rfl
      · 
        simp only [if_neg hx0y0, if_pos] at hlt
        exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · exact absurd rfl hxx'


theorem fcc_rootedSingleCutSeparation_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    fcc_RootedSingleCutSeparation ω n := by
  refine ⟨id, (fun _ => toLex (0, 0)), ?_, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri; exact absurd htri (hno x hxbox)


theorem fcc_rootedSingleCutSeparation_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
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
    fcc_RootedSingleCutSeparation ω n := by
  classical
  set T := tfc_trifFinset ω n with hT
  have hx0T : x₀ ∈ T := tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩
  have hyT : ∀ i, y i ∈ T := fun i => tfc_mem_trifFinset.mpr ⟨(hydata i).1, (hydata i).2.1⟩
  have hx0y : ∀ i, x₀ ≠ y i := fun i => (hydata i).2.2.1
  have hbx0notin : b x₀ ∉ T := stac_infiniteCluster_notMem T ω (hbdata x₀ hx0box htri0).2.2
  have hbynotin : ∀ i, b (y i) ∉ T := fun i =>
    stac_infiniteCluster_notMem T ω (hbdata (y i) (hydata i).1 (hydata i).2.1).2.2
  have hne_bx0 : x₀ ≠ b x₀ := fun h => hbx0notin (h ▸ hx0T)
  have hne_x0_byi : ∀ i, x₀ ≠ b (y i) := fun i h => hbynotin i (h ▸ hx0T)
  have hne_yi_byj : ∀ i j, y i ≠ b (y j) := fun i j h => hbynotin j (h ▸ hyT i)
  have hne_yi_bx0 : ∀ i, y i ≠ b x₀ := fun i h => hbx0notin (h ▸ hyT i)
  have hx0byi : ∀ i, Connected d ω x₀ (b (y i)) := fun i =>
    (hydata i).2.2.2.trans (hbdata (y i) (hydata i).1 (hydata i).2.1).2.1
  have hyi_byi : ∀ i, Connected d ω (y i) (b (y i)) := fun i =>
    (hbdata (y i) (hydata i).1 (hydata i).2.1).2.1
  have hyi_byj : ∀ i j, Connected d ω (y i) (b (y j)) := fun i j =>
    (hydata i).2.2.2.symm.trans (hx0byi j)
  have hx0bx0 : Connected d ω x₀ (b x₀) := (hbdata x₀ hx0box htri0).2.1
  have hyi_bx0 : ∀ i, Connected d ω (y i) (b x₀) := fun i =>
    (hydata i).2.2.2.symm.trans hx0bx0
  
  set rk : Site d → ℕ ×ₗ ℕ :=
    fun z => if z = x₀ then toLex (0, 0)
             else if h : ∃ i, z = y i then toLex (1, (h.choose : ℕ)) else toLex (2, 0) with hrk
  have hrkx0 : rk x₀ = toLex (0, 0) := by simp [hrk]
  have hrkyi : ∀ i, rk (y i) = toLex (1, (i : ℕ)) := by
    intro i
    have hne : y i ≠ x₀ := (hx0y i).symm
    have hex : ∃ j, y i = y j := ⟨i, rfl⟩
    rw [hrk]; simp only [if_neg hne, dif_pos hex]; rw [hyinj hex.choose_spec.symm]
  refine ⟨b, rk, hbdata, ?_, ?_⟩
  · 
    intro x hxbox htri x' hx'box htri' hxx' _hconn
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩
    · rcases hsingle x' hx'box htri' with rfl | ⟨i, rfl⟩
      · exact absurd rfl hxx'
      · rw [hrkx0, hrkyi i]; exact stt_lex_ne_fst (by norm_num)
    · rcases hsingle x' hx'box htri' with rfl | ⟨j, rfl⟩
      · rw [hrkx0, hrkyi i]; exact (stt_lex_ne_fst (by norm_num)).symm
      · rw [hrkyi i, hrkyi j]
        refine stt_lex_ne_snd ?_
        intro hij; exact hxx' (by rw [Fin.val_inj.mp hij])
  · 
    intro x hxbox htri x' hx'box htri' hxx' _hconn hlt
    rcases hsingle x hxbox htri with rfl | ⟨i, rfl⟩
    · rcases hsingle x' hx'box htri' with rfl | ⟨i, rfl⟩
      · exact absurd rfl hxx'
      · 
        refine fsp_sep_of_notSameArm ω (hyi_bx0 i) (hne_yi_bx0 i) (hyi_byi i)
          (hne_yi_byj i i) ?_
        by_cases hji : (j₀ : Fin 3) = i
        · subst hji
          intro hsame
          exact hcentral ((hlyf j₀ (b x) (b (y j₀)) (hyi_bx0 j₀) (hne_yi_bx0 j₀)
            (hyi_byi j₀) (hne_yi_byj j₀ j₀)).mpr hsame)
        · intro hsame
          have hG_bx0 : ly i (b x) = 0 :=
            (hGstar i (b x) hx0bx0 hne_bx0 (hyi_bx0 i) (hne_yi_bx0 i)).mpr
              (by rw [hcx]; exact hji)
          have hG_byi : ly i (b (y i)) ≠ 0 :=
            (not_iff_not.mpr (hGstar i (b (y i)) (hx0byi i) (hne_x0_byi i)
              (hyi_byi i) (hne_yi_byj i i))).mpr (by rw [not_not, hcy i])
          have hcolly : ly i (b x) ≠ ly i (b (y i)) := by
            rw [hG_bx0]; exact fun h => hG_byi h.symm
          exact hcolly ((hlyf i (b x) (b (y i)) (hyi_bx0 i) (hne_yi_bx0 i)
            (hyi_byi i) (hne_yi_byj i i)).mpr hsame)
    · rcases hsingle x' hx'box htri' with rfl | ⟨j, rfl⟩
      · 
        rw [hrkx0, hrkyi i] at hlt
        exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
      · 
        have hij' : i ≠ j := fun h => hxx' (by rw [h])
        refine fsp_sep_of_notSameArm ω (hyi_byj j i) (hne_yi_byj j i) (hyi_byi j)
          (hne_yi_byj j j) ?_
        intro hsame
        have hG_byi : ly j (b (y i)) = 0 :=
          (hGstar j (b (y i)) (hx0byi i) (hne_x0_byi i)
            (hyi_byj j i) (hne_yi_byj j i)).mpr (by rw [hcy i]; exact hij')
        have hG_byj : ly j (b (y j)) ≠ 0 :=
          (not_iff_not.mpr (hGstar j (b (y j)) (hx0byi j) (hne_x0_byi j)
            (hyi_byi j) (hne_yi_byj j j))).mpr (by rw [not_not, hcy j])
        have hcolly : ly j (b (y i)) ≠ ly j (b (y j)) := by
          rw [hG_byi]; exact fun h => hG_byj h.symm
        exact hcolly ((hlyf j (b (y i)) (b (y j)) (hyi_byj j i) (hne_yi_byj j i)
          (hyi_byi j) (hne_yi_byj j j)).mpr hsame)


theorem fcc_rootedSpanningForest_of_claw (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d) (y : Fin 3 → Site d) (lx : Site d → Fin 3) (ly : Fin 3 → Site d → Fin 3)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hydata : ∀ i, y i ∈ box d n ∧ IsTrifurcation d ω (y i) ∧ x₀ ≠ y i ∧
      Connected d ω x₀ (y i))
    (hyinj : Function.Injective y)
    (hlxf : ∀ u v, Connected d ω x₀ u → x₀ ≠ u → Connected d ω x₀ v → x₀ ≠ v →
      (lx u = lx v ↔ fsp_sameArm ω x₀ u v))
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
    stt_RootedSpanningForest ω n :=
  fcc_rootedSpanningForest_of_coverSep ω n
    (fcc_threeArmCover_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlxf hlyf hsingle)
    (fcc_rootedSingleCutSeparation_of_claw ω n x₀ y lx ly hx0box htri0 hydata hyinj hlyf hGstar
      hsingle b hbdata hcy hcx hcentral)

end Percolation
end StatMech
