/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanForestArmsClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BoundaryPruningClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKSpanningTreeClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.OpenSpanningForestClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SecondPeelingClose.Part2
import Def.StatisticalMechanics.Code.Percolation.SpanForestArmsClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem sfa_onBPath_of_arms (ω : ConfigSpace (Sym2 (Site d))) (T : SimpleGraph (Site d))
    (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v) (B : Set (Site d))
    {x ci cj zi zj : Site d}
    (hxci : T.Adj x ci) (hxcj : T.Adj x cj)
    (wi : T.Walk ci zi) (hwix : x ∉ wi.support) (hzi : zi ∈ B)
    (wj : T.Walk cj zj) (hwjx : x ∉ wj.support) (hzj : zj ∈ B)
    (hcut : ¬ Connected d (removeSite x ω) ci cj) :
    spc_OnBPath T B x ∧ spc_OnBPath T B ci ∧ spc_OnBPath T B cj := by
  classical
  
  have hzne : zi ≠ zj := by
    intro h; subst h; apply hcut
    exact (sfa_walk_avoid_connected ω T hπ wi hwix).trans
      (sfa_walk_avoid_connected ω T hπ wj hwjx).symm
  
  set pi : T.Walk ci zi := (wi.toPath : T.Walk ci zi) with hpi
  set pj : T.Walk cj zj := (wj.toPath : T.Walk cj zj) with hpj
  have hpix : x ∉ pi.support := fun h => hwix (wi.support_toPath_subset h)
  have hpjx : x ∉ pj.support := fun h => hwjx (wj.support_toPath_subset h)
  have hdisj : ∀ v, v ∈ pi.support → v ∈ pj.support → False := by
    have := sfa_armWalks_disjoint ω T hπ pi hpix pj hpjx hcut
    exact this
  
  obtain ⟨p, hpp, hxp, hcip, hcjp⟩ :=
    sfa_glue_path hxci hxcj pi (wi.toPath).2 hpix pj (wj.toPath).2 hpjx hdisj
  refine ⟨⟨zi, zj, hzi, hzj, hzne, p, hpp, hxp⟩,
    ⟨zi, zj, hzi, hzj, hzne, p, hpp, hcip⟩,
    ⟨zi, zj, hzi, hzj, hzne, p, hpp, hcjp⟩⟩


theorem sfa_spanForestArms_of_armForestReaching (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : sfa_ArmForestReaching ω n) : spc_SpanForestArms ω n := by
  classical
  obtain ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, hRne, hData⟩ := h
  refine ⟨Vall, T, hTdec, B, c, hTac, hTopen, hTsupp, hBbd, hRne, ?_⟩
  intro x hxbox htri
  obtain ⟨hadj, hcut, hreach⟩ := hData x hxbox htri
  
  obtain ⟨hcut01, hcut02, hcut12⟩ := hcut
  
  have hne01 : c x 0 ≠ c x 1 := fun h => hcut01 (h ▸ connected_refl _ _)
  have hne02 : c x 0 ≠ c x 2 := fun h => hcut02 (h ▸ connected_refl _ _)
  have hne12 : c x 1 ≠ c x 2 := fun h => hcut12 (h ▸ connected_refl _ _)
  
  obtain ⟨hz0, w0, hw0x⟩ := hreach 0
  obtain ⟨hz1, w1, hw1x⟩ := hreach 1
  obtain ⟨hz2, w2, hw2x⟩ := hreach 2
  
  obtain ⟨hxsurv, hc0surv, hc1surv⟩ :=
    sfa_onBPath_of_arms ω T hTopen B (hadj 0) (hadj 1) w0 hw0x hz0 w1 hw1x hz1 hcut01
  obtain ⟨_, _, hc2surv⟩ :=
    sfa_onBPath_of_arms ω T hTopen B (hadj 0) (hadj 2) w0 hw0x hz0 w2 hw2x hz2 hcut02
  refine ⟨hxsurv, ⟨hne01, hne02, hne12⟩, ?_, hcut01, hcut02, hcut12⟩
  intro i
  refine ⟨hadj i, ?_⟩
  fin_cases i
  · exact hc0surv
  · exact hc1surv
  · exact hc2surv


theorem sfa_Tcount_le_boundary_of_armForestReaching (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : sfa_ArmForestReaching ω n) : Tcount d ω n ≤ boxSV_boundaryCard d n :=
  spc_Tcount_le_boundary_of_spanForestArms ω n (sfa_spanForestArms_of_armForestReaching ω n h)


open Classical in

theorem sfa_armForestReaching_of_boundary_edge (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {b₁ b₂ : Site d} (hb1 : b₁ ∈ vertexBoundary d n) (hb2 : b₂ ∈ vertexBoundary d n)
    (hbne : b₁ ≠ b₂) (hopen : (openSubgraph d ω).Adj b₁ b₂)
    (hnotrif : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    sfa_ArmForestReaching ω n := by
  classical
  set T : SimpleGraph (Site d) := SimpleGraph.fromEdgeSet {s(b₁, b₂)} with hT
  have hTb : T.Adj b₁ b₂ := by rw [hT, fromEdgeSet_adj]; exact ⟨by simp, hbne⟩
  have hTac : T.IsAcyclic := by
    rw [hT, isAcyclic_iff_forall_adj_isBridge]
    intro u v huv
    rw [fromEdgeSet_adj] at huv
    obtain ⟨hmem, hne⟩ := huv
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rw [isBridge_iff]
    refine ⟨by rw [fromEdgeSet_adj]; exact ⟨by simp [hmem], hne⟩, ?_⟩
    intro hreach
    obtain ⟨w⟩ := hreach
    have hbot : ((SimpleGraph.fromEdgeSet {s(b₁, b₂)}).deleteEdges {s(u, v)}) = ⊥ := by
      ext a b
      rw [deleteEdges_adj]
      simp only [fromEdgeSet_adj, Set.mem_singleton_iff, Sym2.eq_iff, bot_adj, iff_false, not_and]
      rintro ⟨hab, habne⟩ hnab
      apply hnab
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
        subst_vars <;> tauto
    rw [hbot] at w
    exact hne (w.eq_of_length_eq_zero
      (by cases w with | nil => rfl | cons h _ => exact absurd h (by simp)))
  set B : Set (Site d) := {b₁, b₂} with hB
  set p : T.Walk b₁ b₂ := Walk.cons hTb Walk.nil with hp
  have hpp : p.IsPath := by
    rw [hp, SimpleGraph.Walk.isPath_def]
    change List.Nodup [b₁, b₂]
    simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, List.nodup_nil, and_true]
    exact ⟨hbne, by trivial⟩
  have honB1 : spc_OnBPath T B b₁ :=
    ⟨b₁, b₂, by simp [hB], by simp [hB], hbne, p, hpp, by simp [hp]⟩
  refine ⟨{b₁, b₂}, T, by rw [hT]; infer_instance, B, fun _ _ => b₁, fun _ _ => b₁, hTac,
    ?_, ?_, ?_, ⟨b₁, honB1⟩, ?_⟩
  · intro u v huv
    rw [hT, fromEdgeSet_adj] at huv
    obtain ⟨hmem, hne⟩ := huv
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hopen
    · exact hopen.symm
  · intro u v huv
    rw [hT, fromEdgeSet_adj] at huv
    obtain ⟨hmem, hne⟩ := huv
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  · rw [hB]; intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> assumption
  · intro x hxbox htri; exact absurd htri (hnotrif x hxbox)


open Classical in

theorem sfa_armForestReaching_star (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (a : Fin 3 → Site d)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
    (habdry : ∀ i, a i ∈ vertexBoundary d n)
    (hxne : ∀ i, a i ≠ x)
    (hainj : Function.Injective a)
    (hsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧
            ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧
            ¬ Connected d (removeSite x ω) (a 1) (a 2)) :
    sfa_ArmForestReaching ω n := by
  classical
  set lab : Fin 4 → Site d := fun v => match v with
    | 0 => x | 1 => a 0 | 2 => a 1 | 3 => a 2 with hlab
  have hlabinj : Function.Injective lab := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp only [hlab] at huv <;>
      first
        | rfl
        | (exact absurd huv (hxne 0).symm) | (exact absurd huv (hxne 1).symm)
        | (exact absurd huv (hxne 2).symm) | (exact absurd huv.symm (hxne 0).symm)
        | (exact absurd huv.symm (hxne 1).symm) | (exact absurd huv.symm (hxne 2).symm)
        | (exact absurd (hainj huv) (by decide))
  set emb : Fin 4 ↪ Site d := ⟨lab, hlabinj⟩ with hemb
  set T : SimpleGraph (Site d) := SimpleGraph.map emb Flc2Witness.starG with hT
  have hTac : T.IsAcyclic := spc_map_acyclic Flc2Witness.starG_isTree.isAcyclic emb
  have hTadj : ∀ i j : Fin 4, T.Adj (lab i) (lab j) ↔ Flc2Witness.starG.Adj i j := by
    intro i j; rw [hT, SimpleGraph.map_adj]
    constructor
    · rintro ⟨p, q, hpq, h1, h2⟩; exact (hlabinj h1) ▸ (hlabinj h2) ▸ hpq
    · intro h; exact ⟨i, j, h, rfl, rfl⟩
  have hstar : ∀ i : Fin 3, Flc2Witness.starG.Adj 0 i.succ := by
    intro i; rw [Flc2Witness.starG, fromRel_adj]
    refine ⟨(Fin.succ_ne_zero i).symm, ?_⟩
    left; rw [Flc2Witness.starE]; left; exact ⟨rfl, Fin.succ_ne_zero i⟩
  have hlabsucc : ∀ i : Fin 3, lab i.succ = a i := by intro i; fin_cases i <;> rfl
  have hTxai : ∀ i : Fin 3, T.Adj x (a i) := by
    intro i
    have := (hTadj 0 i.succ).mpr (hstar i)
    rwa [show lab 0 = x from rfl, hlabsucc i] at this
  set B : Set (Site d) := {a 0, a 1, a 2} with hB
  have hai_in_B : ∀ i : Fin 3, a i ∈ B := by intro i; fin_cases i <;> simp [hB]
  
  have hpath01 : ∃ p : T.Walk (a 0) (a 1), p.IsPath ∧ x ∈ p.support := by
    refine ⟨Walk.cons (hTxai 0).symm (Walk.cons (hTxai 1) Walk.nil), ?_, by simp⟩
    rw [SimpleGraph.Walk.isPath_def]
    change List.Nodup [a 0, x, a 1]
    have ha01 : a 0 ≠ a 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hainj h)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
      not_or, and_true]
    exact ⟨⟨hxne 0, ha01⟩, (hxne 1).symm, not_false⟩
  obtain ⟨p01, hp01p, hxp01⟩ := hpath01
  have honB_x : spc_OnBPath T B x :=
    ⟨a 0, a 1, hai_in_B 0, hai_in_B 1, fun h => (by decide : (0 : Fin 3) ≠ 1) (hainj h),
      p01, hp01p, hxp01⟩
  refine ⟨{x, a 0, a 1, a 2}, T, by rw [hT]; infer_instance, B, fun _ => a, fun _ => a, hTac,
    ?_, ?_, ?_, ⟨x, honB_x⟩, ?_⟩
  · 
    intro u v huv
    rw [hT, SimpleGraph.map_adj] at huv
    obtain ⟨p, q, hpq, rfl, rfl⟩ := huv
    rw [Flc2Witness.starG, fromRel_adj] at hpq
    obtain ⟨hpqne, hor⟩ := hpq
    change (openSubgraph d ω).Adj (lab p) (lab q)
    fin_cases p <;> fin_cases q <;> simp only [hlab] <;>
      first
        | (exfalso; revert hor; simp only [Flc2Witness.starE]; decide)
        | exact hadj 0 | exact hadj 1 | exact hadj 2
        | exact (hadj 0).symm | exact (hadj 1).symm | exact (hadj 2).symm
  · 
    intro u v huv
    rw [hT, SimpleGraph.map_adj] at huv
    obtain ⟨p, q, hpq, rfl, rfl⟩ := huv
    fin_cases p <;>
      simp only [Finset.mem_insert, Finset.mem_singleton,
        show (emb : Fin 4 → Site d) = lab from rfl] <;>
      first
        | (left; rfl) | (right; left; rfl) | (right; right; left; rfl) | (right; right; right; rfl)
  · 
    rw [hB]; intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact habdry 0
    · exact habdry 1
    · exact habdry 2
  · 
    intro y hybox htri
    have hyx : y = x := hsingle y hybox htri; subst hyx
    refine ⟨fun i => hTxai i, hsep, ?_⟩
    intro i
    refine ⟨hai_in_B i, Walk.nil, ?_⟩
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]
    exact fun h => (hxne i) h.symm

end Percolation
end StatMech
