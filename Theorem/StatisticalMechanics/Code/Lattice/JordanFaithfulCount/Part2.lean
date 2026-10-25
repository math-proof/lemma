/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFaithfulCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanOuterFaceUnique.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleRank.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFinish.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Def.StatisticalMechanics.Code.Lattice.JordanFaithfulCount
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jfc_whb_count_of_sync (P : PlanarZ2Subgraph) (hsync : jfc_WhbSync P) :
    ∀ (K : SimpleGraph P.V), K ≤ P.G →
      Nat.card (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent = faceCount K := by
  classical
  have hVfin : Finite P.V := P.finV
  have hVdec : DecidableEq P.V := P.decV
  intro K
  generalize hn : K.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    intro hKle
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · 
      subst hz
      have hempty : K.edgeSet = ∅ := (Set.ncard_eq_zero (Set.toFinite K.edgeSet)).mp hn
      have hbot : K = ⊥ := by rw [← edgeSet_eq_empty]; exact hempty
      subst hbot
      rw [jei_pushGraph_bot, jfc_whb_bot]
      have hlat : Nat.card (hypercubicLattice 2).ConnectedComponent = 1 := by
        have hreach : ∀ a b : Site 2, (hypercubicLattice 2).Reachable a b :=
          fun a b => pbs_reach_all a b
        have hsub : Subsingleton (hypercubicLattice 2).ConnectedComponent :=
          ⟨ConnectedComponent.ind₂ (fun a b => ConnectedComponent.sound (hreach a b))⟩
        haveI : Nonempty (hypercubicLattice 2).ConnectedComponent :=
          ⟨(hypercubicLattice 2).connectedComponentMk ![0, 0]⟩
        rw [Nat.card_eq_one_iff_unique]; exact ⟨hsub, inferInstance⟩
      rw [hlat]
      unfold faceCount nullity
      rw [SimpleGraph.edgeSet_bot, Set.ncard_empty, card_components_bot]; simp
    · 
      have hnonempty : K.edgeSet.Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _), hn]; exact hpos
      obtain ⟨e, he⟩ := hnonempty
      obtain ⟨x, y⟩ := e
      set K' := K.deleteEdges {s(x, y)} with hK'
      have hKeq : K = K' ⊔ edge x y := deleteEdges_sup_edge_eq K x y he
      have hadjK : K.Adj x y := by rwa [SimpleGraph.mem_edgeSet] at he
      have hne_xy : x ≠ y := K.ne_of_adj hadjK
      have hadjG : P.G.Adj x y := hKle hadjK
      have hnotK' : ¬ K'.Adj x y := by simp [hK', deleteEdges_adj]
      have hK'le : K' ≤ P.G := (deleteEdges_le _).trans hKle
      have hdrop : K'.edgeSet.ncard + 1 = K.edgeSet.ncard :=
        card_edgeSet_deleteEdges_add_one K x y he
      have hn' : K'.edgeSet.ncard = n - 1 := by omega
      have ihK' : Nat.card (whb_faceRegion (jei_pushGraph P K')).ConnectedComponent = faceCount K' :=
        ih (n - 1) (by omega) K' hn' hK'le
      haveI hfinK' : Finite (whb_faceRegion (jei_pushGraph P K')).ConnectedComponent :=
        jfc_whb_pushGraph_regionComponents_finite P K'
      haveI hfinK : Finite (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent :=
        jfc_whb_pushGraph_regionComponents_finite P K
      set p := P.emb x with hp
      set q := P.emb y with hq
      have hpushEq : jei_pushGraph P K = jei_pushGraph P K' ⊔ edge p q := by
        rw [hKeq, jei_pushGraph_sup_edge P K' x y hne_xy]
      have hpq : p ≠ q := fun h => hne_xy (P.emb.injective h)
      
      have hlatpq : (hypercubicLattice 2).Adj p q := P.isSub hadjG
      obtain ⟨f0, g0, hfg, hshared⟩ := jfc_flankingFaces hlatpq
      have hpres : s(f0, g0) ∈ (whb_faceRegion (jei_pushGraph P K')).edgeSet :=
        jfc_flankingEdge_present P K' hadjG hnotK' hfg hshared
      haveI hfinSup :
          Finite (whb_faceRegion (jei_pushGraph P K' ⊔ edge p q)).ConnectedComponent := by
        rw [← hpushEq]; exact hfinK
      have hdich := jfc_whb_delete_dichotomy (jei_pushGraph P K') (p := p) (q := q)
        (f0 := f0) (g0 := g0) hpq hfg hshared hpres
      have hsyncK' := hsync K' hK'le hadjG hnotK' hfg hshared
      set DR := ((whb_faceRegion (jei_pushGraph P K')).deleteEdges
          {s(f0, g0)}).Reachable f0 g0 with hDR
      have hcardPush : Nat.card (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent
          = Nat.card (whb_faceRegion (jei_pushGraph P K' ⊔ edge p q)).ConnectedComponent := by
        rw [hpushEq]
      by_cases hr : K'.Reachable x y
      · have hnotDR : ¬ DR := hsyncK'.mp hr
        have hdualCard := hdich.2 hnotDR
        have hface : faceCount K = faceCount K' + 1 := by
          rw [hKeq]; exact faceCount_sup_edge_of_reachable K' hne_xy hnotK' hr
        rw [hcardPush, hdualCard, ihK', hface]
      · have hDRtrue : DR := by
          by_contra hcon
          exact hr (hsyncK'.mpr hcon)
        have hdualCard := hdich.1 hDRtrue
        have hface : faceCount K = faceCount K' := by
          rw [hKeq]; exact faceCount_sup_edge_of_not_reachable K' hne_xy hnotK' hr
        rw [hcardPush, hdualCard, ihK', hface]


theorem jfc_imageGraph_support_box (P : PlanarZ2Subgraph) :
    ∀ v ∈ (imageGraph P).support, v ∈ box 2 (outerBoxRadius P) := by
  intro v hv
  rw [SimpleGraph.mem_support] at hv
  obtain ⟨w, hw⟩ := hv
  rw [imageGraph_adj] at hw
  obtain ⟨s, t, _, hs, _⟩ := hw
  rw [← hs]; exact outerBoxRadius_spec P s


end Lattice
end StatMech
