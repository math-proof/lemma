/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part5


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem natCard_orderedFarEndpoint_eq_sum
    (m n t : Nat) (start target : IsingLineBox n)
    (markX targetX : Int) :
    Nat.card (IsingOrderedFarEndpointFamily
        m n t start target markX targetX) =
      ∑ k : Fin (t + 1), ∑ j : Fin k,
        Nat.card (IsingLineFarFirstBoundaryFamily m j) *
        Nat.card (IsingLineFirstEndpointFamily n k start target) *
        Nat.card (VerticalChoicePathFamily (k - j) markX targetX) *
        4 ^ (t - (k : Nat)) := by
  letI (k : Fin (t + 1)) : Fintype (Fin k) := inferInstance
  letI (k : Fin (t + 1)) (j : Fin k) :
      Fintype (IsingLineFarFirstBoundaryFamily m j) := Fintype.ofFinite _
  letI (k : Fin (t + 1)) :
      Fintype (IsingLineFirstEndpointFamily n k start target) :=
    Fintype.ofFinite _
  letI (k : Fin (t + 1)) (j : Fin k) :
      Fintype (VerticalChoicePathFamily (k - j) markX targetX) :=
    Fintype.ofFinite _
  letI (k : Fin (t + 1)) :
      Fintype {tail : List (Bool × Bool) // tail.length = t - k} :=
    (List.finite_length_eq (Bool × Bool) (t - k)).fintype
  unfold IsingOrderedFarEndpointFamily
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.card_prod, Nat.card_prod, Nat.card_prod]
  have htail : Nat.card
      {tail : List (Bool × Bool) // tail.length = t - (k : Nat)} =
      4 ^ (t - (k : Nat)) := by
    change Nat.card (List.Vector (Bool × Bool) (t - (k : Nat))) =
      4 ^ (t - (k : Nat))
    rw [Nat.card_congr
        (Equiv.vectorEquivFin (Bool × Bool) (t - (k : Nat))),
      Nat.card_eq_fintype_card, Fintype.card_fun]
    norm_num
  rw [htail]
  ring


theorem orderedFarEndpoint_weight_eq_sum
    (m n t : Nat) (start target : IsingLineBox n)
    (markX targetX : Int) :
    Nat.card (IsingOrderedFarEndpointFamily
        m n t start target markX targetX) / (4 : Real) ^ t =
      ∑ k : Fin (t + 1), ∑ j : Fin k,
        (Nat.card (IsingLineFarFirstBoundaryFamily m j) /
          (2 : Real) ^ (j : Nat)) *
        (Nat.card (IsingLineFirstEndpointFamily n k start target) /
          (2 : Real) ^ (k : Nat)) *
        (Nat.card (VerticalChoicePathFamily (k - j) markX targetX) /
          (2 : Real) ^ ((k : Nat) - (j : Nat))) := by
  rw [natCard_orderedFarEndpoint_eq_sum]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : (j : Nat) <= (k : Nat) := Nat.le_of_lt j.isLt
  have hfourT : (4 : Real) ^ t =
      (4 : Real) ^ (k : Nat) * (4 : Real) ^ (t - (k : Nat)) := by
    calc
      _ = (4 : Real) ^ ((k : Nat) + (t - (k : Nat))) := by
        congr 1
        exact (Nat.add_sub_of_le (Nat.le_of_lt_succ k.isLt)).symm
      _ = _ := pow_add _ _ _
  have htwoK : (4 : Real) ^ (k : Nat) =
      (2 : Real) ^ (k : Nat) * (2 : Real) ^ (k : Nat) := by
    rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
  have hsplitK : (2 : Real) ^ (k : Nat) =
      (2 : Real) ^ (j : Nat) *
        (2 : Real) ^ ((k : Nat) - (j : Nat)) := by
    calc
      _ = (2 : Real) ^ ((j : Nat) + ((k : Nat) - (j : Nat))) := by
        congr 1
        omega
      _ = _ := pow_add _ _ _
  rw [hfourT, htwoK, hsplitK]
  field_simp


theorem orderedFarEndpoint_weight_le
    (m n t : Nat) (start target : IsingLineBox n)
    (markX targetX : Int) (hm : 0 < m) (ht : t <= m * m)
    (htarget : isingLineBoxBoundary n target) :
    Nat.card (IsingOrderedFarEndpointFamily
        m n t start target markX targetX) / (4 : Real) ^ t <=
      7488 / (m : Real) ^ 2 := by
  let b : Nat -> Real := fun j =>
    Nat.card (IsingLineFarFirstBoundaryFamily m j) / (2 : Real) ^ j
  let v : Nat -> Real := fun k =>
    Nat.card (IsingLineFirstEndpointFamily n k start target) / (2 : Real) ^ k
  let h : Nat -> Real := fun r =>
    Nat.card (VerticalChoicePathFamily r markX targetX) / (2 : Real) ^ r
  have hb0 (j : Nat) : 0 <= b j := by
    dsimp [b]
    positivity
  have hv (k : Nat) (hk : 0 < k) : v k <= 2 / (k : Real) := by
    exact lineFirstEndpoint_boundary_weight_le n k start target hk htarget
  have hh (r : Nat) : h r <= 2 / Real.sqrt (r + 1 : Real) := by
    dsimp [h]
    rw [← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div]
    let K := isingLineBinomialKernel r markX targetX
    have hK0 : 0 <= K := isingLineBinomialKernel_nonneg _ _ _
    have hrad : 0 <= 2 / (r + 1 : Real) := by positivity
    have hK : K <= Real.sqrt (2 / (r + 1 : Real)) := by
      rw [Real.le_sqrt hK0 hrad]
      exact isingLineBinomialKernel_sq_le r markX targetX
    calc
      K <= Real.sqrt (2 / (r + 1 : Real)) := hK
      _ <= 2 / Real.sqrt (r + 1 : Real) := by
        rw [Real.sqrt_div (by positivity)]
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        rw [Real.sqrt_le_iff]
        norm_num
  have hfactor :
      Nat.card (IsingOrderedFarEndpointFamily
          m n t start target markX targetX) / (4 : Real) ^ t =
        ∑ k ∈ Finset.range (t + 1), ∑ j ∈ Finset.range k,
          b j * v k * h (k - j) := by
    rw [orderedFarEndpoint_weight_eq_sum]
    change (∑ k : Fin (t + 1), ∑ j : Fin k,
      b (j : Nat) * v (k : Nat) * h ((k : Nat) - (j : Nat))) = _
    rw [Fin.sum_univ_eq_sum_range
      (fun k : Nat => ∑ j : Fin k, b (j : Nat) * v k * h (k - (j : Nat)))
      (t + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Fin.sum_univ_eq_sum_range
      (fun j : Nat => b j * v k * h (k - j)) k]
  rw [hfactor]
  calc
    (∑ k ∈ Finset.range (t + 1), ∑ j ∈ Finset.range k,
        b j * v k * h (k - j)) <=
        ∑ k ∈ Finset.range (t + 1), ∑ j ∈ Finset.range k,
          b j * (2 / (k : Real)) *
            (2 / Real.sqrt ((k - j + 1 : Nat) : Real)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hbk : 0 <= b j := hb0 j
      calc
        b j * v k * h (k - j) <=
            b j * (2 / (k : Real)) * h (k - j) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left (hv k (by omega)) hbk
          · dsimp [h]
            positivity
        _ <= b j * (2 / (k : Real)) *
            (2 / Real.sqrt ((k - j + 1 : Nat) : Real)) := by
          have hh' : h (k - j) <=
              2 / Real.sqrt ((k - j + 1 : Nat) : Real) := by
            simpa [Nat.cast_add, Nat.cast_one] using hh (k - j)
          apply mul_le_mul_of_nonneg_left hh'
          exact mul_nonneg hbk (by positivity)
    _ = ∑ j ∈ Finset.range (t + 1), b j *
          (∑ l ∈ Finset.range (t - j),
            (2 / ((j + l + 1 : Nat) : Real)) *
              (2 / Real.sqrt ((l + 2 : Nat) : Real))) := by
      let f : Nat -> Nat -> Real := fun j l =>
        b j * ((2 / ((j + l + 1 : Nat) : Real)) *
          (2 / Real.sqrt ((l + 2 : Nat) : Real)))
      rw [Finset.sum_range_succ']
      simp only [Finset.sum_range_zero, sum_empty, add_zero]
      calc
        (∑ k ∈ Finset.range t, ∑ j ∈ Finset.range (k + 1),
            b j * (2 / ((k + 1 : Nat) : Real)) *
              (2 / Real.sqrt ((k + 1 - j + 1 : Nat) : Real))) =
            ∑ k ∈ Finset.range t, ∑ j ∈ Finset.range (k + 1),
              f j (k - j) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro j hj
          have hjk : j <= k := by
            have := Finset.mem_range.mp hj
            omega
          have hden : j + (k - j) + 1 = k + 1 := by omega
          have hgap : k + 1 - j + 1 = k - j + 2 := by omega
          dsimp [f]
          rw [hden, hgap]
          ring
        _ = ∑ j ∈ Finset.range t, ∑ l ∈ Finset.range (t - j),
              f j l := Finset.sum_range_diag_flip t f
        _ = ∑ j ∈ Finset.range (t + 1), b j *
              (∑ l ∈ Finset.range (t - j),
                (2 / ((j + l + 1 : Nat) : Real)) *
                  (2 / Real.sqrt ((l + 2 : Nat) : Real))) := by
          rw [Finset.sum_range_succ]
          simp [f, Finset.mul_sum]
    _ <= 16 * (∑ j ∈ Finset.range (t + 1),
          (2 / Real.sqrt ((j + 1 : Nat) : Real)) * b j) :=
      orderedFarFirstEndpoint_swapped_convolution_le t b hb0
    _ <= 16 * (468 / (m : Real) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa [b, Nat.cast_add, Nat.cast_one] using
        endpointKernel_farFirstBoundary_sum_le m t hm ht
    _ = 7488 / (m : Real) ^ 2 := by ring

theorem orderedFarEndpoint_diffusive_weight_le
    (rho m n : Nat) (start target : IsingLineBox n)
    (markX targetX : Int) (hρ : 0 < rho) (hρm : rho <= m)
    (htarget : isingLineBoxBoundary n target) :
    Nat.card (IsingOrderedFarEndpointFamily
        m n (rho * rho) start target markX targetX) /
        (4 : Real) ^ (rho * rho) <=
      7488 / (rho : Real) ^ 2 := by
  have hm : 0 < m := lt_of_lt_of_le hρ hρm
  have ht : rho * rho <= m * m := Nat.mul_self_le_mul_self hρm
  have hmain := orderedFarEndpoint_weight_le m n (rho * rho)
    start target markX targetX hm ht htarget
  have hsq : (rho : Real) ^ 2 <= (m : Real) ^ 2 := by
    exact_mod_cast (show rho ^ 2 <= m ^ 2 by
      simpa [pow_two] using ht)
  exact hmain.trans
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq)

end
end StatMech.Universality
