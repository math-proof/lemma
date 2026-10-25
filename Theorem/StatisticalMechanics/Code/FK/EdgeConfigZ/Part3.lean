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
import Def.StatisticalMechanics.Code.FK.EdgeConfigZ.Part3
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


section PartitionPeel

variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]


section Peel

variable {T : Type*} [DecidableEq T] (tag : U → T)


theorem ecz_left_eq (τ : T) (S : Finset T) (hτ : τ ∉ S) (p q : ℝ) :
    ecz_fkZEdge (agl_left (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)) p q
      = ecz_fkZEdge (qp_blkG K₀ tag τ) p q := by
  show ecz_fkZEdge (((K₀.comap (Subtype.val : {x // tag x ∈ insert τ S} → U)).comap
    (Subtype.val : {x // tag x.1 = τ} → _))) p q
      = ecz_fkZEdge (K₀.comap (Subtype.val : {x // tag x = τ} → U)) p q
  refine ecz_fkZEdge_iso (qp_comapComapIso K₀ _ _ _ ?_ Subtype.val_injective ?_) p q
  · intro a b h; apply Subtype.ext; apply Subtype.ext; exact h
  · ext u; constructor
    · rintro ⟨v, rfl⟩; exact ⟨⟨v.1, v.2⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨⟨v.1, by rw [v.2]; exact Finset.mem_insert_self τ S⟩, v.2⟩, rfl⟩


theorem ecz_right_eq (τ : T) (S : Finset T) (hτ : τ ∉ S) (p q : ℝ) :
    ecz_fkZEdge (agl_right (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)) p q
      = ecz_fkZEdge (qp_restG K₀ tag S) p q := by
  show ecz_fkZEdge (((K₀.comap (Subtype.val : {x // tag x ∈ insert τ S} → U)).comap
    (Subtype.val : {x // ¬ (tag x.1 = τ)} → _))) p q
      = ecz_fkZEdge (K₀.comap (Subtype.val : {x // tag x ∈ S} → U)) p q
  refine ecz_fkZEdge_iso (qp_comapComapIso K₀ _ _ _ ?_ Subtype.val_injective ?_) p q
  · intro a b h; apply Subtype.ext; apply Subtype.ext; exact h
  · ext u; constructor
    · rintro ⟨v, rfl⟩
      have hv := v.1.2; have hne := v.2; rw [Finset.mem_insert] at hv
      rcases hv with h | h
      · exact absurd h hne
      · exact ⟨⟨v.1.1, h⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨⟨v.1, Finset.mem_insert_of_mem v.2⟩, fun hc => hτ (hc ▸ v.2)⟩, rfl⟩


theorem ecz_left_edge_card (τ : T) (S : Finset T) (hτ : τ ∉ S) :
    (agl_left (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)).edgeFinset.card
      = (qp_blkG K₀ tag τ).edgeFinset.card := by
  show (((K₀.comap (Subtype.val : {x // tag x ∈ insert τ S} → U)).comap
    (Subtype.val : {x // tag x.1 = τ} → _))).edgeFinset.card
      = (K₀.comap (Subtype.val : {x // tag x = τ} → U)).edgeFinset.card
  refine (qp_comapComapIso K₀ _ _ _ ?_ Subtype.val_injective ?_).card_edgeFinset_eq
  · intro a b h; apply Subtype.ext; apply Subtype.ext; exact h
  · ext u; constructor
    · rintro ⟨v, rfl⟩; exact ⟨⟨v.1, v.2⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨⟨v.1, by rw [v.2]; exact Finset.mem_insert_self τ S⟩, v.2⟩, rfl⟩


theorem ecz_right_edge_card (τ : T) (S : Finset T) (hτ : τ ∉ S) :
    (agl_right (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)).edgeFinset.card
      = (qp_restG K₀ tag S).edgeFinset.card := by
  show (((K₀.comap (Subtype.val : {x // tag x ∈ insert τ S} → U)).comap
    (Subtype.val : {x // ¬ (tag x.1 = τ)} → _))).edgeFinset.card
      = (K₀.comap (Subtype.val : {x // tag x ∈ S} → U)).edgeFinset.card
  refine (qp_comapComapIso K₀ _ _ _ ?_ Subtype.val_injective ?_).card_edgeFinset_eq
  · intro a b h; apply Subtype.ext; apply Subtype.ext; exact h
  · ext u; constructor
    · rintro ⟨v, rfl⟩
      have hv := v.1.2; have hne := v.2; rw [Finset.mem_insert] at hv
      rcases hv with h | h
      · exact absurd h hne
      · exact ⟨⟨v.1.1, h⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨⟨v.1, Finset.mem_insert_of_mem v.2⟩, fun hc => hτ (hc ▸ v.2)⟩, rfl⟩


theorem ecz_fkZEdge_empty {V : Type*} [Fintype V] [DecidableEq V] [IsEmpty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p q : ℝ) : ecz_fkZEdge G p q = 1 := by
  have hZ : fkZ G p q = 1 := qp_fkZ_empty G p q
  have hNE : ecz_NE G = 0 := by
    rw [ecz_NE_eq]
    have : Fintype.card (Sym2 V) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun e => e.recOnSubsingleton (fun x => isEmptyElim x)⟩
    omega
  rw [ecz_fkZEdge_eq_div, hZ, hNE, pow_zero, div_one]


theorem ecz_peel_le (p q : ℝ) (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∀ S : Finset T, ∃ I : ℕ,
      ecz_uu (qp_restG K₀ tag S) p q
          ≤ (∑ τ ∈ S, ecz_uu (qp_blkG K₀ tag τ) p q) + (I : ℝ) * (-Real.log (1 - p))
        ∧ I ≤ ∑ τ ∈ S, (qp_straddleEdges K₀ (fun u => tag u = τ)).card := by
  intro S
  induction S using Finset.induction with
  | empty =>
    refine ⟨0, ?_, by simp⟩
    simp only [Finset.sum_empty, Nat.cast_zero, zero_mul, add_zero]
    haveI : IsEmpty {x : U // tag x ∈ (∅ : Finset T)} := ⟨fun x => by simpa using x.2⟩
    rw [ecz_uu, ecz_fkZEdge_empty, Real.log_one, neg_zero]
  | @insert τ S hτ ih =>
    obtain ⟨I0, hI0le, hI0bd⟩ := ih
    have hpart := ecz_neglog_partition_le (qp_restG K₀ tag (insert τ S))
      (fun x => tag x.1 = τ) hp hp1 hq
    rw [show -Real.log (ecz_fkZEdge (agl_left (qp_restG K₀ tag (insert τ S))
            (fun x => tag x.1 = τ)) p q)
        = ecz_uu (qp_blkG K₀ tag τ) p q from by rw [ecz_uu, ecz_left_eq K₀ tag τ S hτ]] at hpart
    rw [show -Real.log (ecz_fkZEdge (agl_right (qp_restG K₀ tag (insert τ S))
            (fun x => tag x.1 = τ)) p q)
        = ecz_uu (qp_restG K₀ tag S) p q from by rw [ecz_uu, ecz_right_eq K₀ tag τ S hτ]] at hpart
    set Istep := agl_interfaceCard (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)
      with hIstep
    refine ⟨Istep + I0, ?_, ?_⟩
    · rw [Finset.sum_insert hτ]; push_cast
      have huu : ecz_uu (qp_restG K₀ tag (insert τ S)) p q
          ≤ ecz_uu (qp_blkG K₀ tag τ) p q + ecz_uu (qp_restG K₀ tag S) p q
            - (Istep : ℝ) * Real.log (1 - p) := by rw [ecz_uu]; exact hpart
      calc ecz_uu (qp_restG K₀ tag (insert τ S)) p q
          ≤ ecz_uu (qp_blkG K₀ tag τ) p q + ecz_uu (qp_restG K₀ tag S) p q
              - (Istep : ℝ) * Real.log (1 - p) := huu
        _ ≤ ecz_uu (qp_blkG K₀ tag τ) p q
              + ((∑ σ ∈ S, ecz_uu (qp_blkG K₀ tag σ) p q) + (I0 : ℝ) * (-Real.log (1 - p)))
              - (Istep : ℝ) * Real.log (1 - p) := by linarith [hI0le]
        _ = (ecz_uu (qp_blkG K₀ tag τ) p q + ∑ σ ∈ S, ecz_uu (qp_blkG K₀ tag σ) p q)
              + ((Istep : ℝ) + (I0 : ℝ)) * (-Real.log (1 - p)) := by ring
    · rw [Finset.sum_insert hτ]
      have hIstepbd : Istep ≤ (qp_straddleEdges K₀ (fun u => tag u = τ)).card :=
        le_trans (qp_interface_le_straddle (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ))
          (qp_restG_straddle_le K₀ tag τ S)
      omega

end Peel
end PartitionPeel
end FK
end StatMech
