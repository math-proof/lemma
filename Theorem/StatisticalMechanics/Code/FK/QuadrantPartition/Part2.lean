/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/QuadrantPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.AdditiveGluing.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Def.StatisticalMechanics.Code.FK.QuadrantPartition.Part4
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

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


variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]


section Peel

variable {T : Type*} [DecidableEq T] (tag : U → T)


theorem qp_fkZ_comapComap {V W X : Type*} [Fintype V] [Fintype X] [DecidableEq V] [DecidableEq X]
    (g : W → U) (f : V → W) (h : X → U) (hgf : Function.Injective (g ∘ f))
    (hh : Function.Injective h) (hr : Set.range (g ∘ f) = Set.range h) (p q : ℝ)
    [DecidableRel ((K₀.comap g).comap f).Adj] [DecidableRel (K₀.comap h).Adj] :
    fkZ ((K₀.comap g).comap f) p q = fkZ (K₀.comap h) p q :=
  fsm_fkZ_iso _ _ (qp_comapComapIso K₀ g f h hgf hh hr) p q


theorem qp_left_eq (τ : T) (S : Finset T) (hτ : τ ∉ S) (p q : ℝ) :
    fkZ (agl_left (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)) p q
      = fkZ (qp_blkG K₀ tag τ) p q := by
  show fkZ (((K₀.comap (Subtype.val : {x // tag x ∈ insert τ S} → U)).comap
    (Subtype.val : {x // tag x.1 = τ} → _))) p q
      = fkZ (K₀.comap (Subtype.val : {x // tag x = τ} → U)) p q
  refine qp_fkZ_comapComap K₀ _ _ _ ?_ Subtype.val_injective ?_ p q
  · intro a b h; apply Subtype.ext; apply Subtype.ext; exact h
  · ext u; constructor
    · rintro ⟨v, rfl⟩; exact ⟨⟨v.1, v.2⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨⟨v.1, by rw [v.2]; exact Finset.mem_insert_self τ S⟩, v.2⟩, rfl⟩


theorem qp_right_eq (τ : T) (S : Finset T) (hτ : τ ∉ S) (p q : ℝ) :
    fkZ (agl_right (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)) p q
      = fkZ (qp_restG K₀ tag S) p q := by
  show fkZ (((K₀.comap (Subtype.val : {x // tag x ∈ insert τ S} → U)).comap
    (Subtype.val : {x // ¬ (tag x.1 = τ)} → _))) p q
      = fkZ (K₀.comap (Subtype.val : {x // tag x ∈ S} → U)) p q
  refine qp_fkZ_comapComap K₀ _ _ _ ?_ Subtype.val_injective ?_ p q
  · intro a b h; apply Subtype.ext; apply Subtype.ext; exact h
  · ext u; constructor
    · rintro ⟨v, rfl⟩
      have hv := v.1.2; have hne := v.2; rw [Finset.mem_insert] at hv
      rcases hv with h | h
      · exact absurd h hne
      · exact ⟨⟨v.1.1, h⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨⟨⟨v.1, Finset.mem_insert_of_mem v.2⟩, fun hc => hτ (hc ▸ v.2)⟩, rfl⟩


theorem qp_interface_le_straddle (P : U → Prop) [DecidablePred P] :
    agl_interfaceCard K₀ P ≤ (qp_straddleEdges K₀ P).card := by
  unfold agl_interfaceCard fis_interface
  apply Finset.card_le_card_of_injOn (fun e => Sym2.map (agl_sumEquiv P) e)
  · intro e he
    rw [Finset.mem_coe, Finset.mem_sdiff, mem_edgeFinset, mem_edgeFinset] at he
    obtain ⟨hK, hnot⟩ := he
    rw [Finset.mem_coe]
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_edgeSet, agl_glueGraph_adj] at hK
      rw [qp_straddleEdges, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · simp only [Sym2.map_pair_eq, mem_edgeFinset, mem_edgeSet]
        match x, y with
        | Sum.inl a, Sum.inl b => simpa only [agl_sumEquiv_inl] using hK
        | Sum.inr c, Sum.inr e => simpa only [agl_sumEquiv_inr] using hK
        | Sum.inl a, Sum.inr e => simpa only [agl_sumEquiv_inl, agl_sumEquiv_inr] using hK
        | Sum.inr c, Sum.inl b => simpa only [agl_sumEquiv_inr, agl_sumEquiv_inl] using hK
      · match x, y with
        | Sum.inl a, Sum.inl b =>
          refine absurd (by rw [mem_edgeSet, SimpleGraph.sum_adj]
                            simpa only [agl_left, comap_adj] using hK) hnot
        | Sum.inr c, Sum.inr e =>
          refine absurd (by rw [mem_edgeSet, SimpleGraph.sum_adj]
                            simpa only [agl_right, comap_adj] using hK) hnot
        | Sum.inl a, Sum.inr e =>
          simp only [Sym2.map_pair_eq, agl_sumEquiv_inl, agl_sumEquiv_inr]
          show qp_straddleP P s((a : U), (e : U))
          rw [qp_straddleP, Sym2.lift_mk]; exact Or.inl ⟨a.2, e.2⟩
        | Sum.inr c, Sum.inl b =>
          simp only [Sym2.map_pair_eq, agl_sumEquiv_inr, agl_sumEquiv_inl]
          show qp_straddleP P s((c : U), (b : U))
          rw [qp_straddleP, Sym2.lift_mk]; exact Or.inr ⟨c.2, b.2⟩
  · intro a _ b _ hab
    exact Sym2.map.injective (Equiv.injective _) hab


theorem qp_restG_straddle_le (τ : T) (S : Finset T) :
    (qp_straddleEdges (qp_restG K₀ tag (insert τ S)) (fun x => tag x.1 = τ)).card
      ≤ (qp_straddleEdges K₀ (fun u => tag u = τ)).card := by
  apply Finset.card_le_card_of_injOn
    (fun e => Sym2.map (Subtype.val : {x // tag x ∈ insert τ S} → U) e)
  · intro e he
    rw [Finset.mem_coe, qp_straddleEdges, Finset.mem_filter] at he
    obtain ⟨hedge, hstr⟩ := he
    rw [Finset.mem_coe, qp_straddleEdges, Finset.mem_filter]
    induction e using Sym2.ind with
    | _ x y =>
      rw [qp_straddleP, Sym2.lift_mk] at hstr
      rw [mem_edgeFinset, mem_edgeSet, qp_restG, comap_adj] at hedge
      refine ⟨?_, ?_⟩
      · simp only [Sym2.map_pair_eq, mem_edgeFinset, mem_edgeSet]; exact hedge
      · simp only [Sym2.map_pair_eq]
        show qp_straddleP (fun u => tag u = τ) s((x : U), (y : U))
        rw [qp_straddleP, Sym2.lift_mk]; exact hstr
  · intro a _ b _ hab
    exact Sym2.map.injective Subtype.val_injective hab


theorem qp_fkZ_empty {V : Type*} [Fintype V] [DecidableEq V] [IsEmpty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (p q : ℝ) : fkZ G p q = 1 := by
  unfold fkZ
  have : Subsingleton (ConfigSpace (Sym2 V)) := by
    constructor; intro a b; funext e; exact e.recOnSubsingleton (fun x => isEmptyElim x)
  rw [Finset.sum_eq_single (fun _ => false)]
  · unfold fkWeight edgeProduct numClusters
    have he : G.edgeFinset = ∅ := by
      rw [SimpleGraph.edgeFinset_eq_empty]; ext a b
      simp only [SimpleGraph.bot_adj]
      exact ⟨fun _ => isEmptyElim a, fun h => h.elim⟩
    rw [he, Finset.prod_empty, one_mul]
    have hc : Fintype.card (openSub G (fun _ => false)).ConnectedComponent = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun c => c.recOnSubsingleton (fun x => isEmptyElim x)⟩
    rw [hc, pow_zero]
  · intro b _ hb; exact absurd (Subsingleton.elim b _) hb
  · intro h; exact absurd (Finset.mem_univ _) h


end Peel
end FK
end StatMech
