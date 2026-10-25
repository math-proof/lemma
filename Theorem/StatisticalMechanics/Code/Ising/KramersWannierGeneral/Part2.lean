/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part4
import Structure.StatisticalMechanics.Code.Ising.KramersWannierGeneral
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section EdgeCrossing

variable {V : Type*} [Fintype V] [DecidableEq V]
  (Gp Gd : SimpleGraph V) [DecidableRel Gp.Adj] [DecidableRel Gd.Adj]


variable {Gp Gd}


theorem cutSpace_subset_edgeFinset {δ : Finset (Sym2 V)} (hδ : δ ∈ cutSpace Gp) :
    δ ⊆ Gp.edgeFinset := by
  rw [cutSpace, Finset.mem_image] at hδ
  obtain ⟨s, _, rfl⟩ := hδ
  unfold cutEdges
  exact Finset.filter_subset _ _


theorem EdgeCrossing.image_mem_even (Φ : EdgeCrossing Gp Gd)
    {δ : Finset (Sym2 V)} (hδ : δ ∈ cutSpace Gp) :
    δ.image Φ.ψ ∈ evenSubgraphs Gd := by
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, Φ.cut_to_even δ hδ⟩
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨a, ha, rfl⟩ := he
  exact Φ.edge_mem a (cutSpace_subset_edgeFinset hδ ha)


theorem EdgeCrossing.invImage_image (Φ : EdgeCrossing Gp Gd)
    (δ : Finset (Sym2 V)) :
    (δ.image Φ.ψ).image Φ.ψ.symm = δ := by
  rw [Finset.image_image]
  have : (Φ.ψ.symm ∘ Φ.ψ) = id := by funext e; simp
  rw [this, Finset.image_id]


theorem EdgeCrossing.image_invImage (Φ : EdgeCrossing Gp Gd)
    (F : Finset (Sym2 V)) :
    (F.image Φ.ψ.symm).image Φ.ψ = F := by
  rw [Finset.image_image]
  have : (Φ.ψ ∘ Φ.ψ.symm) = id := by funext e; simp
  rw [this, Finset.image_id]


theorem EdgeCrossing.card_image (Φ : EdgeCrossing Gp Gd) (δ : Finset (Sym2 V)) :
    (δ.image Φ.ψ).card = δ.card :=
  Finset.card_image_of_injective δ Φ.ψ.injective


theorem EdgeCrossing.hist_eq (Φ : EdgeCrossing Gp Gd) :
    Multiset.map (fun S => S.card) (cutSpace Gp).val
      = Multiset.map (fun S => S.card) (evenSubgraphs Gd).val := by
  
  have himg : evenSubgraphs Gd = (cutSpace Gp).image (fun δ => δ.image Φ.ψ) := by
    ext F
    simp only [Finset.mem_image]
    constructor
    · intro hF
      exact ⟨F.image Φ.ψ.symm, Φ.even_to_cut F hF, Φ.image_invImage F⟩
    · rintro ⟨δ, hδ, rfl⟩
      exact Φ.image_mem_even hδ
  rw [himg]
  
  have hinj : Set.InjOn (fun δ : Finset (Sym2 V) => δ.image Φ.ψ)
      (cutSpace Gp : Set (Finset (Sym2 V))) := by
    intro a _ b _ h
    have := congrArg (fun F => F.image Φ.ψ.symm) h
    simpa only [Φ.invImage_image] using this
  rw [Finset.image_val_of_injOn hinj, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro a ha
  simp only [Function.comp_apply]
  exact (Φ.card_image a).symm


theorem cutMatching_of_edgeCrossing [Nonempty V] (hG : Gp.Preconnected)
    (Φ : EdgeCrossing Gp Gd) (t : ℝ) :
    CutEvenSubgraphMatching Gp Gd t 2 :=
  cutEvenSubgraphMatching_of_hist Gp Gd hG t Φ.hist_eq


theorem isingZ_self_dual_of_edgeCrossing [Nonempty V] (hG : Gp.Preconnected)
    (Φ : EdgeCrossing Gp Gd) (β βstar : ℝ)
    (htemp : Real.tanh βstar = Real.exp (-2 * β)) :
    isingZ Gd βstar 0
      = ((2 : ℝ) ^ Fintype.card V * (Real.cosh βstar) ^ Gd.edgeFinset.card
        / (Real.exp (β * Gp.edgeFinset.card) * 2)) * isingZ Gp β 0 :=
  isingZ_self_dual_of_cutMatching Gp Gd β βstar 2 (by norm_num) htemp
    (cutMatching_of_edgeCrossing hG Φ (Real.exp (-2 * β)))


omit [Fintype V] in


theorem incCount_image_eq_filter (ψ : Sym2 V ≃ Sym2 V) (δ : Finset (Sym2 V)) (w : V) :
    incCount (δ.image ψ) w = (δ.filter (fun e => w ∈ ψ e)).card := by
  unfold incCount
  rw [Finset.filter_image, Finset.card_image_of_injective _ ψ.injective]


theorem cut_to_even_of_faceWalk (ψ : Sym2 V ≃ Sym2 V)
    {basePt : V → V} (faceWalk : (w : V) → Gp.Walk (basePt w) (basePt w))
    (hbridge : ∀ (s : ConfigSpace V) (w : V),
      incCount ((cutEdges Gp s).image ψ) w = walkDis Gp s (faceWalk w)) :
    ∀ δ ∈ cutSpace Gp, IsEvenSubgraph (δ.image ψ) := by
  intro δ hδ
  rw [cutSpace, Finset.mem_image] at hδ
  obtain ⟨s, _, rfl⟩ := hδ
  intro w
  rw [Nat.even_iff, hbridge s w]
  exact walkDis_closed_even Gp s (faceWalk w)

end EdgeCrossing
end Ising
end StatMech
