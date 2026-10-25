/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Def.StatisticalMechanics.Code.Ising.BackboneResummation
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem bbr_restrict_le (n : Current V) (p : Sym2 V → Prop) [DecidablePred p] (e : Sym2 V) :
    restrictCut n p e ≤ n e := by
  unfold restrictCut; by_cases h : p e <;> simp [h]


theorem bbr_cut_split (n : Current V) (p : Sym2 V → Prop) [DecidablePred p] :
    (fun e => restrictCut n p e + restrictCut n (fun e => ¬ p e) e) = n := by
  funext e; unfold restrictCut; by_cases h : p e <;> simp [h]


theorem bbr_weight_cut_factor (β : ℝ) (J : Sym2 V → ℝ) (n : Current V)
    (p : Sym2 V → Prop) [DecidablePred p] :
    Sharpness.weight G β J n
      = Sharpness.weight G β J (restrictCut n p)
        * Sharpness.weight G β J (restrictCut n (fun e => ¬ p e)) := by
  unfold Sharpness.weight restrictCut
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  by_cases h : p e
  · rw [if_pos h, if_neg (not_not_intro h)]; simp
  · rw [if_neg h, if_pos h]; simp


theorem bbr_sources_cut_split (n : Current V) (p : Sym2 V → Prop) [DecidablePred p] :
    Sharpness.sources G n
      = Sharpness.sources G (restrictCut n p)
        ∆ Sharpness.sources G (restrictCut n (fun e => ¬ p e)) := by
  conv_lhs => rw [← bbr_cut_split n p]
  exact sources_add G.edgeFinset (restrictCut n p) (restrictCut n (fun e => ¬ p e))


theorem bbr_mass_eq_weight_mul_count (β : ℝ) (J : Sym2 V → ℝ) (m : Current V) (A : Finset V) :
    hnw_mass G β J m A
      = Sharpness.weight G β J m
        * ∑ K : {K : Current V // ∀ e, K e ≤ m e},
            (if Sharpness.sources G K.1 = A
              then (∏ e ∈ G.edgeFinset, (Nat.choose (m e) (K.1 e) : ℝ)) else 0) :=
  hnw_mass_eq_weight_mul_count G β J m A


theorem bbr_mass_nonneg (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : Current V) (S : Finset V) : 0 ≤ hnw_mass G β J m S :=
  hnw_mass_nonneg G β J hβ hJ m S


theorem bbr_inj_domination {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (f : α → ℝ) (g : β → ℝ) (Ψ : α → β)
    (hΨmem : ∀ a ∈ S, Ψ a ∈ T)
    (hΨinj : ∀ a ∈ S, ∀ a' ∈ S, Ψ a = Ψ a' → a = a')
    (hgnn : ∀ b ∈ T, 0 ≤ g b)
    (hbound : ∀ a ∈ S, 2 * f a ≤ g (Ψ a)) :
    2 * (∑ a ∈ S, f a) ≤ ∑ b ∈ T, g b := by
  have h1 : 2 * (∑ a ∈ S, f a) ≤ ∑ a ∈ S, g (Ψ a) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun a ha => hbound a ha)
  have h2 : ∑ a ∈ S, g (Ψ a) = ∑ b ∈ S.image Ψ, g b := by
    rw [Finset.sum_image]; intro a ha a' ha' h; exact hΨinj a ha a' ha' h
  have h3 : ∑ b ∈ S.image Ψ, g b ≤ ∑ b ∈ T, g b := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro b hb; rw [Finset.mem_image] at hb; obtain ⟨a, ha, rfl⟩ := hb; exact hΨmem a ha
    · intro b hb _; exact hgnn b hb
  rw [h2] at h1; linarith


end Ising
end StatMech
