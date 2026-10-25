/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokalFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.EsCorrelations.Part4
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem esWeight_spinsum_factor_q {q : ℕ} (p : ℝ) (ω : ConfigSpace (Sym2 V))
    (g : (V → Fin q) → ℝ) :
    (∑ σ : V → Fin q, esWeight G p σ ω * g σ)
      = edgeProduct G p ω
        * ∑ σ : V → Fin q, (if ConstOnOpen G ω σ then (1 : ℝ) else 0) * g σ := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [esWeight_factor, monoProd_eq_indicator]
  ring


theorem card_constEq_real_conn {q : ℕ} (ω : ConfigSpace (Sym2 V)) {x y : V}
    (hxy : Connected G ω x y) :
    ((Finset.univ.filter (fun σ : V → Fin q => ConstOnOpen G ω σ ∧ σ x = σ y)).card : ℝ)
      = (q : ℝ) ^ numClusters G ω := by
  have hc := card_constEq_connected (q := q) G ω hxy
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
  rw [hc]; push_cast; ring


theorem card_constEq_real_disc {q : ℕ} (ω : ConfigSpace (Sym2 V)) {x y : V}
    (hxy : ¬ Connected G ω x y) :
    ((Finset.univ.filter (fun σ : V → Fin q => ConstOnOpen G ω σ ∧ σ x = σ y)).card : ℝ)
      = (q : ℝ) ^ (numClusters G ω - 1) := by
  have hc := card_constEq_disconnected (q := q) G ω hxy
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
  rw [hc]; push_cast; ring


theorem spinAgree_sum_eq {q : ℕ} [NeZero q] (p : ℝ) (ω : ConfigSpace (Sym2 V)) (x y : V) :
    (∑ σ : V → Fin q, esWeight G p σ ω * (if σ x = σ y then (1 : ℝ) else 0))
      = if Connected G ω x y then fkWeight G p (q : ℝ) ω
        else fkWeight G p (q : ℝ) ω / q := by
  rw [esWeight_spinsum_factor_q]
  have hinner : (∑ σ : V → Fin q,
        (if ConstOnOpen G ω σ then (1 : ℝ) else 0) * (if σ x = σ y then (1 : ℝ) else 0))
      = ((Finset.univ.filter (fun σ : V → Fin q => ConstOnOpen G ω σ ∧ σ x = σ y)).card : ℝ) := by
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hc : ConstOnOpen G ω σ <;> by_cases he : σ x = σ y <;> simp [hc, he]
  rw [hinner]
  by_cases h : Connected G ω x y
  · rw [if_pos h, card_constEq_real_conn G ω h]
    unfold fkWeight; ring
  · rw [if_neg h, card_constEq_real_disc G ω h]
    have hqne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    have hk : 1 ≤ numClusters G ω := one_le_numClusters G ω x
    unfold fkWeight
    rw [mul_div_assoc]
    congr 1
    rw [eq_div_iff hqne, mul_comm ((q : ℝ) ^ (numClusters G ω - 1)) (q : ℝ), ← pow_succ']
    congr 1
    omega


end FK
end StatMech
