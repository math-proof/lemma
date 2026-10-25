/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Theorem.StatisticalMechanics.Code.FK.CenteredFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Def.StatisticalMechanics.Code.FK.EdgeConfigZ.Part8
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


section BoxNesting

variable {d : ℕ}


theorem ecz_box_nesting_le (a n : ℕ) (hle : a ≤ n) (t : ℝ) :
    ecz_u d t n ≤ ecz_u d t a
      + ((agl_interfaceCard (boxGraph d n) (ecz_subBoxPred d a n)
          + ((agl_right (boxGraph d n) (ecz_subBoxPred d a n)).edgeFinset.card : ℝ)))
          * (-Real.log (1 - fsc_logistic t)) := by
  classical
  set p := fsc_logistic t with hp
  have hp0 : (0 : ℝ) < p := fsc_logistic_pos t
  have hp1 : p < 1 := fsc_logistic_lt_one t
  set c := -Real.log (1 - p) with hc
  have hc0 : 0 ≤ c := by rw [hc, neg_nonneg]; exact Real.log_nonpos (by linarith) (by linarith)
  set P : boxVerts d n → Prop := ecz_subBoxPred d a n with hP
  have hpart := ecz_neglog_partition_le (boxGraph d n) P hp0 hp1 (by norm_num : (0:ℝ) < 2)
  have hleft : ecz_fkZEdge (agl_left (boxGraph d n) P) p 2 = ecz_fkZEdge (boxGraph d a) p 2 :=
    (ecz_fkZEdge_iso (ecz_subBoxIso a n hle) p 2).symm
  have hright : -Real.log (ecz_fkZEdge (agl_right (boxGraph d n) P) p 2)
      ≤ ((agl_right (boxGraph d n) P).edgeFinset.card : ℝ) * c :=
    ecz_neglogZEdge_le_edges _ hp0 hp1 (by norm_num)
  rw [ecz_u, ecz_u]
  rw [show -Real.log (ecz_fkZEdge (agl_left (boxGraph d n) P) p 2)
        = -Real.log (ecz_fkZEdge (boxGraph d a) p 2) from by rw [hleft]] at hpart
  have hkey : -Real.log (ecz_fkZEdge (boxGraph d n) p 2)
      ≤ -Real.log (ecz_fkZEdge (boxGraph d a) p 2)
        + ((agl_right (boxGraph d n) P).edgeFinset.card : ℝ) * c
        + (agl_interfaceCard (boxGraph d n) P : ℝ) * c := by
    have hceq : -(agl_interfaceCard (boxGraph d n) P : ℝ) * Real.log (1 - p)
        = (agl_interfaceCard (boxGraph d n) P : ℝ) * c := by rw [hc]; ring
    nlinarith [hpart, hright, hceq]
  calc -Real.log (ecz_fkZEdge (boxGraph d n) p 2)
      ≤ _ := hkey
    _ = -Real.log (ecz_fkZEdge (boxGraph d a) p 2)
        + ((agl_interfaceCard (boxGraph d n) P : ℝ)
            + ((agl_right (boxGraph d n) P).edgeFinset.card : ℝ)) * c := by ring


theorem ecz_sum_edgeFinset_card {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    (G ⊕g H).edgeFinset.card = G.edgeFinset.card + H.edgeFinset.card := by
  classical
  have hkey : (G ⊕g H).edgeFinset
      = G.edgeFinset.image (Sym2.map Sum.inl) ∪ H.edgeFinset.image (Sym2.map Sum.inr) := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Finset.mem_union, Finset.mem_image, mem_edgeFinset, mem_edgeSet]
      match x, y with
      | Sum.inl a, Sum.inl b =>
        constructor
        · intro h
          refine Or.inl ⟨s(a, b), ?_, by simp [Sym2.map_mk]⟩
          rw [mem_edgeSet]; rw [SimpleGraph.sum_adj] at h; exact h
        · rintro (⟨f, hf, hfe⟩ | ⟨f, hf, hfe⟩)
          · induction f using Sym2.ind with
            | _ p q =>
              rw [mem_edgeSet] at hf
              simp only [Sym2.map_mk] at hfe
              rcases Sym2.eq_iff.mp hfe with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
                (simp only [Sum.inl.injEq] at h1 h2; subst h1; subst h2)
              · rw [SimpleGraph.sum_adj]; exact hf
              · rw [SimpleGraph.sum_adj]; exact hf.symm
          · induction f using Sym2.ind with
            | _ p q => simp only [Sym2.map_mk] at hfe; exact absurd hfe (by simp)
      | Sum.inr c, Sum.inr e2 =>
        constructor
        · intro h
          refine Or.inr ⟨s(c, e2), ?_, by simp [Sym2.map_mk]⟩
          rw [mem_edgeSet]; rw [SimpleGraph.sum_adj] at h; exact h
        · rintro (⟨f, hf, hfe⟩ | ⟨f, hf, hfe⟩)
          · induction f using Sym2.ind with
            | _ p q => simp only [Sym2.map_mk] at hfe; exact absurd hfe (by simp)
          · induction f using Sym2.ind with
            | _ p q =>
              rw [mem_edgeSet] at hf
              simp only [Sym2.map_mk] at hfe
              rcases Sym2.eq_iff.mp hfe with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
                (simp only [Sum.inr.injEq] at h1 h2; subst h1; subst h2)
              · rw [SimpleGraph.sum_adj]; exact hf
              · rw [SimpleGraph.sum_adj]; exact hf.symm
      | Sum.inl a, Sum.inr d =>
        constructor
        · intro h; rw [SimpleGraph.sum_adj] at h; exact absurd h not_false
        · rintro (⟨f, hf, hfe⟩ | ⟨f, hf, hfe⟩) <;>
          · induction f using Sym2.ind with
            | _ p q => simp only [Sym2.map_mk] at hfe; exact absurd hfe (by simp)
      | Sum.inr c, Sum.inl b =>
        constructor
        · intro h; rw [SimpleGraph.sum_adj] at h; exact absurd h not_false
        · rintro (⟨f, hf, hfe⟩ | ⟨f, hf, hfe⟩) <;>
          · induction f using Sym2.ind with
            | _ p q => simp only [Sym2.map_mk] at hfe; exact absurd hfe (by simp)
  have hinjL : Function.Injective (Sym2.map (Sum.inl : V → V ⊕ W)) :=
    Sym2.map.injective Sum.inl_injective
  have hinjR : Function.Injective (Sym2.map (Sum.inr : W → V ⊕ W)) :=
    Sym2.map.injective Sum.inr_injective
  have hdisj : Disjoint (G.edgeFinset.image (Sym2.map Sum.inl))
      (H.edgeFinset.image (Sym2.map Sum.inr)) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [Finset.mem_image, mem_edgeFinset] at he1 he2
    obtain ⟨f1, _, hf1⟩ := he1
    obtain ⟨f2, _, hf2⟩ := he2
    induction f1 using Sym2.ind with
    | _ p q =>
      induction f2 using Sym2.ind with
      | _ r t =>
        simp only [Sym2.map_mk] at hf1 hf2
        rw [← hf2] at hf1
        rcases Sym2.eq_iff.mp hf1 with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact absurd h1 (by simp)
  calc (G ⊕g H).edgeFinset.card
      = (G.edgeFinset.image (Sym2.map Sum.inl) ∪ H.edgeFinset.image (Sym2.map Sum.inr)).card := by
          rw [hkey]
    _ = (G.edgeFinset.image (Sym2.map Sum.inl)).card
          + (H.edgeFinset.image (Sym2.map Sum.inr)).card := Finset.card_union_of_disjoint hdisj
    _ = G.edgeFinset.card + H.edgeFinset.card := by
          rw [Finset.card_image_of_injective _ hinjL, Finset.card_image_of_injective _ hinjR]


theorem ecz_partition_edge_card {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U)
    [DecidableRel K₀.Adj] (P : U → Prop) [DecidablePred P] :
    K₀.edgeFinset.card
      = (agl_left K₀ P).edgeFinset.card + (agl_right K₀ P).edgeFinset.card
        + agl_interfaceCard K₀ P := by
  classical
  have hiso : K₀.edgeFinset.card = (agl_glueGraph K₀ P).edgeFinset.card :=
    (agl_iso K₀ P).card_edgeFinset_eq
  have hci := agl_partitionCrossInterface K₀ P
  have heq := fis_edgeFinset_eq hci
  have hdisj : Disjoint ((agl_left K₀ P ⊕g agl_right K₀ P).edgeFinset)
      (fis_interface (agl_left K₀ P) (agl_right K₀ P) (agl_glueGraph K₀ P)) := by
    rw [fis_interface]; exact Finset.disjoint_sdiff
  rw [hiso, heq, Finset.card_union_of_disjoint hdisj, agl_interfaceCard,
    ecz_sum_edgeFinset_card]


section MultiBlock

variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]
  {T : Type*} [DecidableEq T] (tag : U → T)


theorem ecz_peel_edge_card (τ : T) (S : Finset T) (hτ : τ ∉ S) :
    (qp_restG K₀ tag (insert τ S)).edgeFinset.card
      = (qp_blkG K₀ tag τ).edgeFinset.card + (qp_restG K₀ tag S).edgeFinset.card
        + agl_interfaceCard (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ) := by
  have hpc := ecz_partition_edge_card (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)
  rw [ecz_left_edge_card K₀ tag τ S hτ, ecz_right_edge_card K₀ tag τ S hτ] at hpc
  exact hpc


theorem ecz_multiblock_subadd (p q : ℝ) (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∀ S : Finset T,
      ecz_uu (qp_restG K₀ tag S) p q
        ≤ (∑ τ ∈ S, ecz_uu (qp_blkG K₀ tag τ) p q)
          + (((qp_restG K₀ tag S).edgeFinset.card : ℝ)
              - ∑ τ ∈ S, ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ)) * (-Real.log (1 - p)) := by
  intro S
  induction S using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty, sub_zero]
    haveI : IsEmpty {x : U // tag x ∈ (∅ : Finset T)} := ⟨fun x => by simpa using x.2⟩
    have hcard : (qp_restG K₀ tag (∅ : Finset T)).edgeFinset.card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro e he; rw [mem_edgeFinset] at he
      induction e using Sym2.ind with | _ x y => exact isEmptyElim x
    rw [ecz_uu, ecz_fkZEdge_empty, Real.log_one, neg_zero, hcard]
    simp
  | @insert τ S hτ ih =>
    have hpart := ecz_neglog_partition_le (qp_restG K₀ tag (insert τ S))
      (fun x => tag x.1 = τ) hp hp1 hq
    rw [show -Real.log (ecz_fkZEdge (agl_left (qp_restG K₀ tag (insert τ S))
            (fun x => tag x.1 = τ)) p q)
        = ecz_uu (qp_blkG K₀ tag τ) p q from by rw [ecz_uu, ecz_left_eq K₀ tag τ S hτ]] at hpart
    rw [show -Real.log (ecz_fkZEdge (agl_right (qp_restG K₀ tag (insert τ S))
            (fun x => tag x.1 = τ)) p q)
        = ecz_uu (qp_restG K₀ tag S) p q from by rw [ecz_uu, ecz_right_eq K₀ tag τ S hτ]] at hpart
    set c := -Real.log (1 - p) with hc
    set Istep := agl_interfaceCard (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ) with hIstep
    
    have hedge := ecz_peel_edge_card K₀ tag τ S hτ
    have hedgeR : ((qp_restG K₀ tag (insert τ S)).edgeFinset.card : ℝ)
        = ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ) + ((qp_restG K₀ tag S).edgeFinset.card : ℝ)
          + (Istep : ℝ) := by rw [← hIstep] at hedge; exact_mod_cast hedge
    
    have huu : ecz_uu (qp_restG K₀ tag (insert τ S)) p q
        ≤ ecz_uu (qp_blkG K₀ tag τ) p q + ecz_uu (qp_restG K₀ tag S) p q + (Istep : ℝ) * c := by
      have : ecz_uu (qp_restG K₀ tag (insert τ S)) p q
          ≤ ecz_uu (qp_blkG K₀ tag τ) p q + ecz_uu (qp_restG K₀ tag S) p q
            - (Istep : ℝ) * Real.log (1 - p) := by rw [ecz_uu]; exact hpart
      rw [hc]; linarith [this]
    rw [Finset.sum_insert hτ, Finset.sum_insert hτ]
    set A : ℝ := ecz_uu (qp_blkG K₀ tag τ) p q with hA
    set B : ℝ := ∑ σ ∈ S, ecz_uu (qp_blkG K₀ tag σ) p q with hB
    set CardI : ℝ := ((qp_restG K₀ tag (insert τ S)).edgeFinset.card : ℝ) with hCardI
    set CardS : ℝ := ((qp_restG K₀ tag S).edgeFinset.card : ℝ) with hCardS
    set Cblk : ℝ := ((qp_blkG K₀ tag τ).edgeFinset.card : ℝ) with hCblk
    set Csum : ℝ := ∑ σ ∈ S, ((qp_blkG K₀ tag σ).edgeFinset.card : ℝ) with hCsum
    
    have hih : ecz_uu (qp_restG K₀ tag S) p q ≤ B + (CardS - Csum) * c := by rw [hc]; exact ih
    
    have hcoeff : (CardI - (Cblk + Csum)) * c = (Istep : ℝ) * c + (CardS - Csum) * c := by
      rw [hedgeR]; ring
    rw [hcoeff]
    calc ecz_uu (qp_restG K₀ tag (insert τ S)) p q
        ≤ A + ecz_uu (qp_restG K₀ tag S) p q + (Istep : ℝ) * c := huu
      _ ≤ A + (B + (CardS - Csum) * c) + (Istep : ℝ) * c := by linarith [hih]
      _ = A + B + ((Istep : ℝ) * c + (CardS - Csum) * c) := by ring

end MultiBlock


theorem ecz_box_annulus_card (a n : ℕ) (hle : a ≤ n) :
    (agl_interfaceCard (boxGraph d n) (ecz_subBoxPred d a n)
        + (agl_right (boxGraph d n) (ecz_subBoxPred d a n)).edgeFinset.card)
      + (boxGraph d a).edgeFinset.card = (boxGraph d n).edgeFinset.card := by
  classical
  have hpc := ecz_partition_edge_card (boxGraph d n) (ecz_subBoxPred d a n)
  have hleftcard : (agl_left (boxGraph d n) (ecz_subBoxPred d a n)).edgeFinset.card
      = (boxGraph d a).edgeFinset.card := (ecz_subBoxIso a n hle).card_edgeFinset_eq.symm
  rw [hleftcard] at hpc
  omega


theorem ecz_box_nesting_le' (a n : ℕ) (hle : a ≤ n) (t : ℝ) :
    ecz_u d t n ≤ ecz_u d t a
      + (((boxGraph d n).edgeFinset.card : ℝ) - ((boxGraph d a).edgeFinset.card : ℝ))
          * (-Real.log (1 - fsc_logistic t)) := by
  have hnest := ecz_box_nesting_le (d := d) a n hle t
  have hcard := ecz_box_annulus_card (d := d) a n hle
  have hcardR : ((agl_interfaceCard (boxGraph d n) (ecz_subBoxPred d a n) : ℝ)
      + ((agl_right (boxGraph d n) (ecz_subBoxPred d a n)).edgeFinset.card : ℝ))
      = ((boxGraph d n).edgeFinset.card : ℝ) - ((boxGraph d a).edgeFinset.card : ℝ) := by
    have hc : ((agl_interfaceCard (boxGraph d n) (ecz_subBoxPred d a n)
        + (agl_right (boxGraph d n) (ecz_subBoxPred d a n)).edgeFinset.card : ℕ) : ℝ)
        + ((boxGraph d a).edgeFinset.card : ℝ) = ((boxGraph d n).edgeFinset.card : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hcard
    push_cast at hc ⊢; linarith
  rw [hcardR] at hnest
  exact hnest


theorem ecz_box_nesting_sandwich (a n b : ℕ) (han : a ≤ n) (hnb : n ≤ b) (t : ℝ) :
    ecz_u d t b
        - ((agl_interfaceCard (boxGraph d b) (ecz_subBoxPred d n b)
            + ((agl_right (boxGraph d b) (ecz_subBoxPred d n b)).edgeFinset.card : ℝ)))
            * (-Real.log (1 - fsc_logistic t))
        ≤ ecz_u d t n
      ∧ ecz_u d t n ≤ ecz_u d t a
        + ((agl_interfaceCard (boxGraph d n) (ecz_subBoxPred d a n)
            + ((agl_right (boxGraph d n) (ecz_subBoxPred d a n)).edgeFinset.card : ℝ)))
            * (-Real.log (1 - fsc_logistic t)) := by
  have hb := ecz_box_nesting_le (d := d) n b hnb t
  have ha := ecz_box_nesting_le (d := d) a n han t
  exact ⟨by linarith [hb], ha⟩


theorem ecz_box_nesting_sandwich' (a n b : ℕ) (han : a ≤ n) (hnb : n ≤ b) (t : ℝ) :
    ecz_u d t b
        - (((boxGraph d b).edgeFinset.card : ℝ) - ((boxGraph d n).edgeFinset.card : ℝ))
            * (-Real.log (1 - fsc_logistic t))
        ≤ ecz_u d t n
      ∧ ecz_u d t n ≤ ecz_u d t a
        + (((boxGraph d n).edgeFinset.card : ℝ) - ((boxGraph d a).edgeFinset.card : ℝ))
            * (-Real.log (1 - fsc_logistic t)) := by
  have hb := ecz_box_nesting_le' (d := d) n b hnb t
  have ha := ecz_box_nesting_le' (d := d) a n han t
  exact ⟨by linarith [hb], ha⟩


end BoxNesting
end FK
end StatMech
