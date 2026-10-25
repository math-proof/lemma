/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EdwardsSokalClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
import Theorem.StatisticalMechanics.Code.FK.Potts.Part6
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
open scoped BigOperators

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem esk_esWeight_spinsum_factor {q : ℕ} (p : ℝ) (ω : ConfigSpace (Sym2 V))
    (g : (V → Fin q) → ℝ) :
    (∑ σ : V → Fin q, esWeight G p σ ω * g σ)
      = edgeProduct G p ω
        * ∑ σ : V → Fin q, (if ConstOnOpen G ω σ then (1 : ℝ) else 0) * g σ := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [esWeight_factor, monoProd_eq_indicator]
  ring


theorem esk_agree_spinsum_card {q : ℕ} (p : ℝ) (ω : ConfigSpace (Sym2 V)) (x y : V) :
    (∑ σ : V → Fin q, esWeight G p σ ω * (if σ x = σ y then (1:ℝ) else 0))
      = edgeProduct G p ω *
        ((Finset.univ.filter (fun σ : V → Fin q => ConstOnOpen G ω σ ∧ σ x = σ y)).card : ℝ) := by
  rw [esk_esWeight_spinsum_factor]
  congr 1
  rw [← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hc : ConstOnOpen G ω σ
  · by_cases he : σ x = σ y
    · rw [if_pos hc, if_pos he, if_pos (And.intro hc he)]; ring
    · rw [if_pos hc, if_neg he,
        if_neg (show ¬(ConstOnOpen G ω σ ∧ σ x = σ y) from fun h => he h.2)]
      ring
  · rw [if_neg hc, if_neg (show ¬(ConstOnOpen G ω σ ∧ σ x = σ y) from fun h => hc h.1)]; ring


theorem esk_agree_spinsum_fkWeight {q : ℕ} (hq : 0 < q) (p : ℝ)
    (ω : ConfigSpace (Sym2 V)) (x y : V) :
    (∑ σ : V → Fin q, esWeight G p σ ω * (if σ x = σ y then (1:ℝ) else 0))
      = if Connected G ω x y then fkWeight G p (q:ℝ) ω
        else fkWeight G p (q:ℝ) ω / (q:ℝ) := by
  rw [esk_agree_spinsum_card]
  by_cases h : Connected G ω x y
  · rw [if_pos h]
    have hc := card_constEq_connected (q := q) G ω h
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
    rw [hc]
    unfold fkWeight
    push_cast
    ring
  · rw [if_neg h]
    have hc := card_constEq_disconnected (q := q) G ω h
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
    rw [hc]
    unfold fkWeight
    have hk : 1 ≤ numClusters G ω := one_le_numClusters G ω x
    have hqr : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hpow : (q:ℝ) ^ numClusters G ω = (q:ℝ) * (q:ℝ) ^ (numClusters G ω - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hpow]
    field_simp
    push_cast
    ring


end FK
end StatMech
