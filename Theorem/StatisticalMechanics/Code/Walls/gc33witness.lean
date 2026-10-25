/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc31surgery.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc32surgery
import Theorem.StatisticalMechanics.Code.Ising.BackboneResummation.Part2
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Ising.HdomMultiplicity.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc33_split_card (m : Sharpness.Current V) :
    Fintype.card {K : Sharpness.Current V // ∀ e, K e ≤ m e} = ∏ e : Sym2 V, (m e + 1) := by
  rw [Fintype.card_congr (show {K : Sharpness.Current V // ∀ e, K e ≤ m e}
        ≃ (Π e : Sym2 V, Fin (m e + 1)) from
    { toFun := fun K => fun e => ⟨K.1 e, Nat.lt_succ_of_le (K.2 e)⟩
      invFun := fun f => ⟨fun e => (f e).1, fun e => Nat.le_of_lt_succ (f e).2⟩
      left_inv := fun K => by ext e; simp
      right_inv := fun f => by ext e; simp })]
  rw [Fintype.card_pi]; simp


theorem gc33_split_term_eq (β : ℝ) (J : Sym2 V → ℝ) (m : Sharpness.Current V)
    (h01 : ∀ e ∈ G.edgeFinset, m e ≤ 1) (K : Sharpness.Current V) (hK : ∀ e, K e ≤ m e) :
    Sharpness.weight G β J K * Sharpness.weight G β J (fun e => m e - K e)
      = Sharpness.weight G β J m := by
  rw [Sharpness.weight_mul_eq G β J K (fun e => m e - K e)]
  have hsum : (fun e => K e + (m e - K e)) = m := by funext e; exact Nat.add_sub_cancel' (hK e)
  rw [hsum]
  have hprod : (∏ e ∈ G.edgeFinset, (Nat.choose (K e + (m e - K e)) (K e) : ℝ)) = 1 := by
    apply Finset.prod_eq_one; intro e he
    have hme : m e ≤ 1 := h01 e he
    have heq : K e + (m e - K e) = m e := Nat.add_sub_cancel' (hK e)
    rw [heq]
    have hKe : K e ≤ 1 := le_trans (hK e) hme
    interval_cases hK' : K e <;> interval_cases hM' : m e <;> simp_all
  rw [hprod, one_mul]


theorem gc33_mass_le (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (m : Sharpness.Current V) (h01 : ∀ e ∈ G.edgeFinset, m e ≤ 1) (S : Finset V) :
    hnw_mass G β J m S
      ≤ (Fintype.card {K : Sharpness.Current V // ∀ e, K e ≤ m e} : ℝ)
        * Sharpness.weight G β J m := by
  unfold hnw_mass splitWeightedSum
  calc ∑ K : {K : Sharpness.Current V // ∀ e, K e ≤ m e},
          (if Sharpness.sources G K.1 = S
            then (1:ℝ) * (Sharpness.weight G β J K.1
              * Sharpness.weight G β J (fun e => m e - K.1 e))
            else 0)
      ≤ ∑ K : {K : Sharpness.Current V // ∀ e, K e ≤ m e}, Sharpness.weight G β J m := by
        apply Finset.sum_le_sum
        intro K _
        by_cases h : Sharpness.sources G K.1 = S
        · rw [if_pos h, one_mul, gc33_split_term_eq G β J m h01 K.1 K.2]
        · rw [if_neg h, ← gc33_split_term_eq G β J m h01 K.1 K.2]
          exact mul_nonneg (asd_weight_nonneg G β J hβ hJ _) (asd_weight_nonneg G β J hβ hJ _)
    _ = (Fintype.card {K : Sharpness.Current V // ∀ e, K e ≤ m e} : ℝ)
          * Sharpness.weight G β J m := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]


theorem gc33_connP_isolated {P : Finset (Sym2 V)} {a : V} (ha : ∀ e ∈ P, a ∉ e) {b : V}
    (h : connP P a b) : a = b := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      subst ih
      obtain ⟨e, he, hae, _, _⟩ := hstep
      exact absurd hae (ha e he)


end StatMech.Walls
