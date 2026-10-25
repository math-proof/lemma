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
import Def.StatisticalMechanics.Code.Percolation.ForestColouringClose2.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem fcc_removeSite_self_eq (ω : ConfigSpace (Sym2 (Site d))) {y v : Site d}
    (h : Connected d (removeSite y ω) y v) : v = y := by
  have h' : Connected d (removeSites {y} ω) y v := by rwa [daep_removeSites_singleton]
  exact stac_removeSites_connected_eq {y} ω (Finset.mem_singleton_self y) h'


theorem fcc_two_distinct_arms (ω : ConfigSpace (Sym2 (Site d))) {y : Site d}
    (htri : IsTrifurcation d ω y) :
    ∃ u v, (Connected d ω y u ∧ y ≠ u) ∧ (Connected d ω y v ∧ y ≠ v) ∧
      ¬ fsp_sameArm ω y u v := by
  obtain ⟨a₁, a₂, a₃, ⟨h12, h13, h23⟩, ⟨hc1, hc2, hc3⟩, _hinf, ⟨hd12, hd13, hd23⟩⟩ := htri
  by_cases e1 : y = a₁
  · have ne2 : y ≠ a₂ := fun h => h12 (e1.symm.trans h)
    have ne3 : y ≠ a₃ := fun h => h13 (e1.symm.trans h)
    exact ⟨a₂, a₃, ⟨hc2, ne2⟩, ⟨hc3, ne3⟩, fcc_notSameArm_of_singleCut ω hc2 ne2 hc3 ne3 hd23⟩
  · by_cases e2 : y = a₂
    · have ne3 : y ≠ a₃ := fun h => h23 (e2.symm.trans h)
      exact ⟨a₁, a₃, ⟨hc1, e1⟩, ⟨hc3, ne3⟩, fcc_notSameArm_of_singleCut ω hc1 e1 hc3 ne3 hd13⟩
    · exact ⟨a₁, a₂, ⟨hc1, e1⟩, ⟨hc2, e2⟩, fcc_notSameArm_of_singleCut ω hc1 e1 hc2 e2 hd12⟩


theorem fcc_threeArmCover_of_faithful (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (c : Site d → Site d → Fin 3)
    (hcolor : ∀ y, y ∈ box d n → IsTrifurcation d ω y → ∀ u v,
      Connected d ω y u → y ≠ u → Connected d ω y v → y ≠ v →
      (c y u = c y v ↔ fsp_sameArm ω y u v)) :
    fcc_ThreeArmCover ω n := by
  classical
  refine ⟨fcc_colorRep ω c, ?_⟩
  intro y hybox htriy
  have hrep_real : ∀ i, (∃ w, Connected d ω y w ∧ y ≠ w ∧ c y w = i) →
      Connected d ω y (fcc_colorRep ω c y i) ∧ y ≠ fcc_colorRep ω c y i ∧
      c y (fcc_colorRep ω c y i) = i := by
    intro i hex
    rw [fcc_colorRep, dif_pos hex]; exact hex.choose_spec
  
  have hcover : ∀ w, Connected d ω y w → y ≠ w →
      ∃ i, Connected d (removeSite y ω) (fcc_colorRep ω c y i) (fsp_armWitness ω y w) := by
    intro w hyw hnew
    refine ⟨c y w, ?_⟩
    have hex : ∃ w', Connected d ω y w' ∧ y ≠ w' ∧ c y w' = c y w := ⟨w, hyw, hnew, rfl⟩
    obtain ⟨hr_conn, hr_ne, hr_col⟩ := hrep_real (c y w) hex
    have hsame : fsp_sameArm ω y (fcc_colorRep ω c y (c y w)) w :=
      (hcolor y hybox htriy _ _ hr_conn hr_ne hyw hnew).mp hr_col
    unfold fsp_sameArm at hsame
    have hwr : Connected d (removeSite y ω) (fsp_armWitness ω y (fcc_colorRep ω c y (c y w)))
        (fcc_colorRep ω c y (c y w)) := fsp_armWitness_inArm ω hr_conn hr_ne
    exact hwr.symm.trans hsame
  
  have hsep : ∀ i j, i ≠ j →
      ¬ Connected d (removeSite y ω) (fcc_colorRep ω c y i) (fcc_colorRep ω c y j) := by
    intro i j hij hconn
    by_cases hi : ∃ w, Connected d ω y w ∧ y ≠ w ∧ c y w = i
    · by_cases hj : ∃ w, Connected d ω y w ∧ y ≠ w ∧ c y w = j
      · obtain ⟨hi_conn, hi_ne, hi_col⟩ := hrep_real i hi
        obtain ⟨hj_conn, hj_ne, hj_col⟩ := hrep_real j hj
        have hcd : c y (fcc_colorRep ω c y i) ≠ c y (fcc_colorRep ω c y j) := by
          rw [hi_col, hj_col]; exact hij
        have hns : ¬ fsp_sameArm ω y (fcc_colorRep ω c y i) (fcc_colorRep ω c y j) := fun hsame =>
          hcd ((hcolor y hybox htriy _ _ hi_conn hi_ne hj_conn hj_ne).mpr hsame)
        apply hns
        unfold fsp_sameArm
        have hwi : Connected d (removeSite y ω) (fsp_armWitness ω y (fcc_colorRep ω c y i))
            (fcc_colorRep ω c y i) := fsp_armWitness_inArm ω hi_conn hi_ne
        have hwj : Connected d (removeSite y ω) (fsp_armWitness ω y (fcc_colorRep ω c y j))
            (fcc_colorRep ω c y j) := fsp_armWitness_inArm ω hj_conn hj_ne
        exact hwi.trans (hconn.trans hwj.symm)
      · obtain ⟨_, hi_ne, _⟩ := hrep_real i hi
        have hjy : fcc_colorRep ω c y j = y := by rw [fcc_colorRep, dif_neg hj]
        rw [hjy] at hconn
        exact hi_ne (fcc_removeSite_self_eq ω hconn.symm).symm
    · have hiy : fcc_colorRep ω c y i = y := by rw [fcc_colorRep, dif_neg hi]
      rw [hiy] at hconn
      have hjy : fcc_colorRep ω c y j = y := fcc_removeSite_self_eq ω hconn
      by_cases hj : ∃ w, Connected d ω y w ∧ y ≠ w ∧ c y w = j
      · obtain ⟨_, hj_ne, _⟩ := hrep_real j hj
        exact hj_ne hjy.symm
      · 
        obtain ⟨u, v, ⟨hyu, hneu⟩, ⟨hyv, hnev⟩, huv⟩ := fcc_two_distinct_arms ω htriy
        have hcuv : c y u ≠ c y v := fun hce =>
          huv ((hcolor y hybox htriy u v hyu hneu hyv hnev).mp hce)
        have hu_i : c y u ≠ i := fun he => hi ⟨u, hyu, hneu, he⟩
        have hu_j : c y u ≠ j := fun he => hj ⟨u, hyu, hneu, he⟩
        have hv_i : c y v ≠ i := fun he => hi ⟨v, hyv, hnev, he⟩
        have hv_j : c y v ≠ j := fun he => hj ⟨v, hyv, hnev, he⟩
        have hle : ({c y u, c y v, i, j} : Finset (Fin 3)).card ≤ Fintype.card (Fin 3) :=
          Finset.card_le_univ _
        have hcard : ({c y u, c y v, i, j} : Finset (Fin 3)).card = 4 := by
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
            Finset.card_insert_of_notMem, Finset.card_singleton]
          · rw [Finset.mem_singleton]; exact hij
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hv_i, hv_j⟩
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hcuv, hu_i, hu_j⟩
        rw [hcard, Fintype.card_fin] at hle
        omega
  exact ⟨hsep, hcover⟩


theorem fcc_rootedSpanningForest_of_coverSep (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcov : fcc_ThreeArmCover ω n) (hsep : fcc_RootedSingleCutSeparation ω n) :
    stt_RootedSpanningForest ω n := by
  classical
  obtain ⟨arms, harms⟩ := hcov
  obtain ⟨b, rank, hbdata, hrank, hbsep⟩ := hsep
  refine ⟨b, rank, (fun y => stac_colorOf ω y (arms y)), hbdata, ?_, hrank, ?_⟩
  · 
    intro y hybox htriy u v hyu hneu hyv hnev
    obtain ⟨hsep', hcov'⟩ := harms y hybox htriy
    exact stac_colorOf_faithful ω y (arms y) hsep' hcov' hyu hneu hyv hnev
  · 
    intro x hxbox htri y hybox htriy hxy hconn hlt
    have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
    have hbxnotin : b x ∉ tfc_trifFinset ω n :=
      stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω (hbdata x hxbox htri).2.2
    have hbynotin : b y ∉ tfc_trifFinset ω n :=
      stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω (hbdata y hybox htriy).2.2
    have hne_y_bx : y ≠ b x := fun heq => hbxnotin (heq ▸ hyT)
    have hne_y_by : y ≠ b y := fun heq => hbynotin (heq ▸ hyT)
    have hy_bx : Connected d ω y (b x) := hconn.symm.trans (hbdata x hxbox htri).2.1
    have hy_by : Connected d ω y (b y) := (hbdata y hybox htriy).2.1
    have hsingleCut : ¬ Connected d (removeSite y ω) (b x) (b y) :=
      hbsep x hxbox htri y hybox htriy hxy hconn hlt
    have hdiv : ¬ fsp_sameArm ω y (b x) (b y) :=
      fcc_notSameArm_of_singleCut ω hy_bx hne_y_bx hy_by hne_y_by hsingleCut
    obtain ⟨hsep', hcov'⟩ := harms y hybox htriy
    intro hcoleq
    exact hdiv
      ((stac_colorOf_faithful ω y (arms y) hsep' hcov' hy_bx hne_y_bx hy_by hne_y_by).mp hcoleq)


theorem fcc_threeArmCover_of_rootedSpanningForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : stt_RootedSpanningForest ω n) : fcc_ThreeArmCover ω n := by
  obtain ⟨_b, _rank, c, _hbdata, hcolor, _hinj, _hdiv⟩ := h
  exact fcc_threeArmCover_of_faithful ω n c hcolor


theorem fcc_rootedSingleCutSeparation_of_rootedSpanningForest (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (h : stt_RootedSpanningForest ω n) : fcc_RootedSingleCutSeparation ω n := by
  classical
  obtain ⟨b, rank, c, hbdata, hcolor, hinj, hdiv⟩ := h
  refine ⟨b, rank, hbdata, hinj, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  have hcoldiff : c y (b x) ≠ c y (b y) := hdiv x hxbox htri y hybox htriy hxy hconn hlt
  have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
  have hbxnotin : b x ∉ tfc_trifFinset ω n :=
    stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω (hbdata x hxbox htri).2.2
  have hbynotin : b y ∉ tfc_trifFinset ω n :=
    stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω (hbdata y hybox htriy).2.2
  have hne_y_bx : y ≠ b x := fun heq => hbxnotin (heq ▸ hyT)
  have hne_y_by : y ≠ b y := fun heq => hbynotin (heq ▸ hyT)
  have hy_bx : Connected d ω y (b x) := hconn.symm.trans (hbdata x hxbox htri).2.1
  have hy_by : Connected d ω y (b y) := (hbdata y hybox htriy).2.1
  have hns : ¬ fsp_sameArm ω y (b x) (b y) := by
    intro hsame
    exact hcoldiff ((hcolor y hybox htriy (b x) (b y) hy_bx hne_y_bx hy_by hne_y_by).mpr hsame)
  exact fsp_sep_of_notSameArm ω hy_bx hne_y_bx hy_by hne_y_by hns


theorem fcc_rootedSpanningForest_iff (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    stt_RootedSpanningForest ω n ↔
      (fcc_ThreeArmCover ω n ∧ fcc_RootedSingleCutSeparation ω n) :=
  ⟨fun h => ⟨fcc_threeArmCover_of_rootedSpanningForest ω n h,
      fcc_rootedSingleCutSeparation_of_rootedSpanningForest ω n h⟩,
    fun ⟨hcov, hsep⟩ => fcc_rootedSpanningForest_of_coverSep ω n hcov hsep⟩


end Percolation
end StatMech
