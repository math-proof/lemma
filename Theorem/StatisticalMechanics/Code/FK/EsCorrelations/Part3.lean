/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EsCorrelations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FK.EsCorrelations.Part4
open scoped BigOperators

set_option linter.style.show false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem card_constEq_connected {q : ℕ} (ω : ConfigSpace (Sym2 V)) {x y : V}
    (hxy : Connected G ω x y) :
    Nat.card {σ : V → Fin q // ConstOnOpen G ω σ ∧ σ x = σ y} = q ^ numClusters G ω := by
  rw [Nat.card_congr (constEqEquiv G ω x y),
    card_eqfun_eq q (SimpleGraph.ConnectedComponent.eq.2 hxy)]
  rfl


theorem card_constEq_disconnected {q : ℕ} (ω : ConfigSpace (Sym2 V)) {x y : V}
    (hxy : ¬ Connected G ω x y) :
    Nat.card {σ : V → Fin q // ConstOnOpen G ω σ ∧ σ x = σ y}
      = q ^ (numClusters G ω - 1) := by
  have hne : (openSub G ω).connectedComponentMk x ≠ (openSub G ω).connectedComponentMk y := by
    rw [Ne, SimpleGraph.ConnectedComponent.eq]; exact hxy
  rw [Nat.card_congr (constEqEquiv G ω x y), card_eqfun_ne q hne]
  rfl


theorem one_le_numClusters (ω : ConfigSpace (Sym2 V)) (x : V) : 1 ≤ numClusters G ω := by
  unfold numClusters
  rw [Nat.one_le_iff_ne_zero, Ne, Fintype.card_eq_zero_iff]
  intro h
  exact h.false ((openSub G ω).connectedComponentMk x)


theorem card_const_two (ω : ConfigSpace (Sym2 V)) :
    ((Finset.univ.filter (fun σ : V → Fin 2 => ConstOnOpen G ω σ)).card : ℝ)
      = 2 ^ numClusters G ω := by
  have h := card_constOnOpen (q := 2) G ω
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  rw [h]; push_cast; ring


theorem esWeight_spinsum_factor (p : ℝ) (ω : ConfigSpace (Sym2 V)) (g : (V → Fin 2) → ℝ) :
    (∑ σ : V → Fin 2, esWeight G p σ ω * g σ)
      = edgeProduct G p ω
        * ∑ σ : V → Fin 2, (if ConstOnOpen G ω σ then (1 : ℝ) else 0) * g σ := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [esWeight_factor, monoProd_eq_indicator]
  ring


theorem inner_spin_sum (ω : ConfigSpace (Sym2 V)) (x y : V) :
    (∑ σ : V → Fin 2,
        (if ConstOnOpen G ω σ then (1 : ℝ) else 0) * (isingSpin (σ x) * isingSpin (σ y)))
      = 2 * (Finset.univ.filter (fun σ : V → Fin 2 => ConstOnOpen G ω σ ∧ σ x = σ y)).card
        - (Finset.univ.filter (fun σ : V → Fin 2 => ConstOnOpen G ω σ)).card := by
  have hpt : ∀ σ : V → Fin 2,
      (if ConstOnOpen G ω σ then (1 : ℝ) else 0) * (isingSpin (σ x) * isingSpin (σ y))
        = 2 * (if ConstOnOpen G ω σ ∧ σ x = σ y then (1 : ℝ) else 0)
          - (if ConstOnOpen G ω σ then (1 : ℝ) else 0) := by
    intro σ
    rw [isingSpin_mul]
    by_cases hc : ConstOnOpen G ω σ
    · by_cases he : σ x = σ y
      · rw [if_pos hc, if_pos he, if_pos (And.intro hc he)]; ring
      · rw [if_pos hc, if_neg he,
          if_neg (show ¬(ConstOnOpen G ω σ ∧ σ x = σ y) from fun h => he h.2)]; ring
    · rw [if_neg hc, if_neg (show ¬(ConstOnOpen G ω σ ∧ σ x = σ y) from fun h => hc h.1)]; ring
  rw [Finset.sum_congr rfl (fun σ _ => hpt σ)]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole]


theorem spinProd_sum_eq (p : ℝ) (ω : ConfigSpace (Sym2 V)) (x y : V) :
    (∑ σ : V → Fin 2, esWeight G p σ ω * (isingSpin (σ x) * isingSpin (σ y)))
      = if Connected G ω x y then fkWeight G p (2 : ℝ) ω else 0 := by
  rw [esWeight_spinsum_factor, inner_spin_sum, card_const_two G ω]
  by_cases h : Connected G ω x y
  · rw [if_pos h]
    have hcard :
        ((Finset.univ.filter (fun σ : V → Fin 2 => ConstOnOpen G ω σ ∧ σ x = σ y)).card : ℝ)
          = 2 ^ numClusters G ω := by
      have hc := card_constEq_connected (q := 2) G ω h
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
      rw [hc]; push_cast; ring
    rw [hcard]
    unfold fkWeight
    ring
  · rw [if_neg h]
    have hcard :
        ((Finset.univ.filter (fun σ : V → Fin 2 => ConstOnOpen G ω σ ∧ σ x = σ y)).card : ℝ)
          = 2 ^ (numClusters G ω - 1) := by
      have hc := card_constEq_disconnected (q := 2) G ω h
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
      rw [hc]; push_cast; ring
    rw [hcard]
    
    
    have hk : 1 ≤ numClusters G ω := one_le_numClusters G ω x
    have hpow : (2 : ℝ) ^ numClusters G ω = 2 * 2 ^ (numClusters G ω - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hpow]
    ring


end FK
end StatMech
