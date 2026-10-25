/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFourthMoment
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part4


namespace StatMech.Universality

open Finset

noncomputable section

theorem lineFirstBoundary_partial_weight_le_stopped
    (m K : Nat) (hm : 0 < m) :
    (∑ j ∈ Finset.range (K + 1),
      (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) /
        (2 : Real) ^ j) ≤
      isingLineStoppedKernel (2 * m) K ⟨m, by omega⟩ ⟨0, by omega⟩ +
        isingLineStoppedKernel (2 * m) K ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ := by
  have hcard : Nat.card (EndpointFirstBoundaryExtension m K) ≤
      Nat.card (EndpointBoundaryStringFamily m K) :=
    Nat.card_le_card_of_injective (endpointFirstBoundaryExtend m K)
      (endpointFirstBoundaryExtend_injective m K)
  have hext : Nat.card (EndpointFirstBoundaryExtension m K) =
      ∑ j : Fin (K + 1),
        Nat.card (IsingLineFirstBoundaryFamily m j) * 2 ^ (K - j) := by
    letI (j : Fin (K + 1)) :
        Fintype (IsingLineFirstBoundaryFamily m j) := Fintype.ofFinite _
    letI (j : Fin (K + 1)) :
        Fintype {tail : List Bool // tail.length = K - j} :=
      (List.finite_length_eq Bool (K - j)).fintype
    change Nat.card (Σ j : Fin (K + 1),
      IsingLineFirstBoundaryFamily m j ×
        {tail : List Bool // tail.length = K - j}) = _
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.card_prod]
    congr 1
    change Nat.card (List.Vector Bool (K - (j : Nat))) = 2 ^ (K - (j : Nat))
    rw [Nat.card_congr (Equiv.vectorEquivFin Bool (K - (j : Nat))),
      Nat.card_eq_fintype_card, Fintype.card_fun]
    simp
  have hboundary : Nat.card (EndpointBoundaryStringFamily m K) =
      Nat.card (IsingLineChoicePathFamily (2 * m) K
          ⟨m, by omega⟩ ⟨0, by omega⟩) +
        Nat.card (IsingLineChoicePathFamily (2 * m) K
          ⟨m, by omega⟩ ⟨2 * m, by omega⟩) := by
    rw [Nat.card_congr (endpointBoundaryStringEquivSum m K hm), Nat.card_sum]
  have hweightedNat :
      (∑ j : Fin (K + 1),
        Nat.card (IsingLineFirstBoundaryFamily m j) * 2 ^ (K - j)) ≤
          Nat.card (EndpointBoundaryStringFamily m K) := by
    rw [← hext]
    exact hcard
  have hweightedReal :
      (∑ j : Fin (K + 1),
        (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
          (2 : Real) ^ (K - j)) ≤
          (Nat.card (EndpointBoundaryStringFamily m K) : Real) := by
    exact_mod_cast hweightedNat
  rw [Fin.sum_univ_eq_sum_range
    (fun j : Nat => (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
      (2 : Real) ^ (K - j)) (K + 1)] at hweightedReal
  have htwo : 0 < (2 : Real) ^ K := by positivity
  have hdiv := div_le_div_of_nonneg_right hweightedReal htwo.le
  calc
    (∑ j ∈ Finset.range (K + 1),
      (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) /
        (2 : Real) ^ j) =
      (∑ j ∈ Finset.range (K + 1),
        (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
          (2 : Real) ^ (K - j)) / (2 : Real) ^ K := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      have hjK : j ≤ K := by
        have := Finset.mem_range.mp hj
        omega
      have hpow : (2 : Real) ^ K =
          (2 : Real) ^ j * (2 : Real) ^ (K - j) := by
        calc
          (2 : Real) ^ K = (2 : Real) ^ (j + (K - j)) := by
            congr 1
            omega
          _ = _ := pow_add _ _ _
      calc
        (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) /
            (2 : Real) ^ j =
          ((Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
            (2 : Real) ^ (K - j)) /
              ((2 : Real) ^ j * (2 : Real) ^ (K - j)) :=
            (mul_div_mul_right _ _ (by positivity)).symm
        _ = _ := by rw [hpow]
    _ ≤ (Nat.card (EndpointBoundaryStringFamily m K) : Real) /
        (2 : Real) ^ K := hdiv
    _ = isingLineStoppedKernel (2 * m) K ⟨m, by omega⟩ ⟨0, by omega⟩ +
        isingLineStoppedKernel (2 * m) K ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ := by
      rw [hboundary]
      push_cast
      rw [add_div]
      rw [isingLineStoppedKernel_eq_natCard_choicePath_div,
        isingLineStoppedKernel_eq_natCard_choicePath_div]


theorem lineFirstBoundary_partial_weight_le_fourth
    (m K : Nat) (hm : 0 < m) :
    (∑ j ∈ Finset.range (K + 1),
      (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) /
        (2 : Real) ^ j) ≤
      3 * (K : Real) ^ 2 / (m : Real) ^ 4 :=
  (lineFirstBoundary_partial_weight_le_stopped m K hm).trans
    (isingLineStoppedKernel_center_boundary_le_fourth m K hm)

theorem endpointRace_sum_mul_eq_last_partial_add
    (a b : Nat → Real) (N : Nat) :
    (∑ k ∈ Finset.range (N + 1), a k * b k) =
      a N * (∑ k ∈ Finset.range (N + 1), b k) +
        ∑ k ∈ Finset.range N,
          (a k - a (k + 1)) *
            (∑ j ∈ Finset.range (k + 1), b j) := by
  induction N with
  | zero => simp
  | succ N ih =>
      calc
        (∑ k ∈ Finset.range (N + 1 + 1), a k * b k) =
            (∑ k ∈ Finset.range (N + 1), a k * b k) +
              a (N + 1) * b (N + 1) := by rw [Finset.sum_range_succ]
        _ = (a N * (∑ k ∈ Finset.range (N + 1), b k) +
              ∑ k ∈ Finset.range N,
                (a k - a (k + 1)) *
                  (∑ j ∈ Finset.range (k + 1), b j)) +
              a (N + 1) * b (N + 1) := by rw [ih]
        _ = a (N + 1) * (∑ k ∈ Finset.range (N + 1 + 1), b k) +
              ∑ k ∈ Finset.range (N + 1),
                (a k - a (k + 1)) *
                  (∑ j ∈ Finset.range (k + 1), b j) := by
            have hbSucc : (∑ k ∈ Finset.range (N + 1 + 1), b k) =
                (∑ k ∈ Finset.range (N + 1), b k) + b (N + 1) := by
              rw [Finset.sum_range_succ]
            have hdSucc :
                (∑ k ∈ Finset.range (N + 1),
                  (a k - a (k + 1)) *
                    (∑ j ∈ Finset.range (k + 1), b j)) =
                  (∑ k ∈ Finset.range N,
                    (a k - a (k + 1)) *
                      (∑ j ∈ Finset.range (k + 1), b j)) +
                    (a N - a (N + 1)) *
                      (∑ j ∈ Finset.range (N + 1), b j) := by
              rw [Finset.sum_range_succ]
            rw [hbSucc, hdSucc]
            ring


theorem endpointBallot_firstBoundary_sum_le
    (m N : Nat) (hm : 0 < m) (hN : N ≤ m * m) :
    (∑ k ∈ Finset.range (N + 1),
      (4 / (k + 1 : Real)) *
        ((Nat.card (IsingLineFirstBoundaryFamily m k) : Real) /
          (2 : Real) ^ k)) ≤
      24 / (m : Real) ^ 2 := by
  let a : Nat → Real := fun k => 4 / (k + 1 : Real)
  let b : Nat → Real := fun k =>
    (Nat.card (IsingLineFirstBoundaryFamily m k) : Real) / (2 : Real) ^ k
  have hm2 : 0 < (m : Real) ^ 2 := by positivity
  have hm4 : 0 < (m : Real) ^ 4 := by positivity
  have hNReal : (N : Real) ≤ (m : Real) ^ 2 := by
    exact_mod_cast (show N ≤ m ^ 2 by simpa [pow_two] using hN)
  have hpartial (k : Nat) :
      (∑ j ∈ Finset.range (k + 1), b j) ≤
        3 * (k : Real) ^ 2 / (m : Real) ^ 4 := by
    simpa [b] using lineFirstBoundary_partial_weight_le_fourth m k hm
  have hlast :
      a N * (∑ k ∈ Finset.range (N + 1), b k) ≤
        12 / (m : Real) ^ 2 := by
    calc
      _ ≤ a N * (3 * (N : Real) ^ 2 / (m : Real) ^ 4) := by
        apply mul_le_mul_of_nonneg_left (hpartial N)
        dsimp [a]
        positivity
      _ ≤ 12 / (m : Real) ^ 2 := by
        dsimp [a]
        have hN1 : (0 : Real) < N + 1 := by positivity
        have hN2 : (N : Real) ^ 2 ≤
            (N + 1 : Real) * (m : Real) ^ 2 := by
          have hmul := mul_le_mul hNReal
            (show (N : Real) ≤ N + 1 by norm_num)
            (by positivity) (by positivity)
          nlinarith
        have hN2mul := mul_le_mul_of_nonneg_right hN2 hm2.le
        calc
          4 / (N + 1 : Real) *
                (3 * (N : Real) ^ 2 / (m : Real) ^ 4) =
              12 * (N : Real) ^ 2 /
                ((N + 1 : Real) * (m : Real) ^ 4) := by
            field_simp
            ring
          _ ≤ 12 / (m : Real) ^ 2 := by
            rw [div_le_div_iff₀ (mul_pos hN1 hm4) hm2]
            have hmul12 := mul_le_mul_of_nonneg_left hN2mul
              (show (0 : Real) ≤ 12 by norm_num)
            convert hmul12 using 1 <;> ring
  have hterm (k : Nat) :
      (a k - a (k + 1)) *
          (∑ j ∈ Finset.range (k + 1), b j) ≤
        12 / (m : Real) ^ 4 := by
    have hdiff : 0 ≤ a k - a (k + 1) := by
      dsimp [a]
      have hk1 : (0 : Real) < k + 1 := by positivity
      have hk2 : (0 : Real) < k + 2 := by positivity
      apply sub_nonneg.mpr
      exact div_le_div_of_nonneg_left (by norm_num) hk1 (by norm_num)
    calc
      _ ≤ (a k - a (k + 1)) *
          (3 * (k : Real) ^ 2 / (m : Real) ^ 4) :=
        mul_le_mul_of_nonneg_left (hpartial k) hdiff
      _ ≤ 12 / (m : Real) ^ 4 := by
        dsimp [a]
        norm_num [Nat.cast_add, Nat.cast_one]
        have hk1 : (0 : Real) < k + 1 := by positivity
        have hk2 : (0 : Real) < (k : Real) + 1 + 1 := by positivity
        have hkSq : (k : Real) ^ 2 ≤
            ((k : Real) + 1) * ((k : Real) + 1 + 1) := by
          nlinarith [show (0 : Real) ≤ k by positivity]
        have hkSqMul := mul_le_mul_of_nonneg_right hkSq hm4.le
        calc
          (4 / ((k : Real) + 1) - 4 / ((k : Real) + 1 + 1)) *
                (3 * (k : Real) ^ 2 / (m : Real) ^ 4) =
              12 * (k : Real) ^ 2 /
                ((((k : Real) + 1) * ((k : Real) + 1 + 1)) *
                  (m : Real) ^ 4) := by
            field_simp
            ring
          _ ≤ 12 / (m : Real) ^ 4 := by
            rw [div_le_div_iff₀ (mul_pos (mul_pos hk1 hk2) hm4) hm4]
            have hmul12 := mul_le_mul_of_nonneg_left hkSqMul
              (show (0 : Real) ≤ 12 by norm_num)
            convert hmul12 using 1 <;> ring
  rw [show (∑ k ∈ Finset.range (N + 1),
      (4 / (k + 1 : Real)) *
        ((Nat.card (IsingLineFirstBoundaryFamily m k) : Real) /
          (2 : Real) ^ k)) =
      ∑ k ∈ Finset.range (N + 1), a k * b k by rfl]
  rw [endpointRace_sum_mul_eq_last_partial_add]
  calc
    _ ≤ 12 / (m : Real) ^ 2 +
        ∑ k ∈ Finset.range N, 12 / (m : Real) ^ 4 := by
      exact add_le_add hlast (Finset.sum_le_sum fun k hk => hterm k)
    _ = 12 / (m : Real) ^ 2 +
        (N : Real) * (12 / (m : Real) ^ 4) := by
      rw [Finset.sum_const, Finset.card_range]
      simp [nsmul_eq_mul]
    _ ≤ 12 / (m : Real) ^ 2 + 12 / (m : Real) ^ 2 := by
      apply add_le_add (le_refl _)
      calc
        (N : Real) * (12 / (m : Real) ^ 4) ≤
            (m : Real) ^ 2 * (12 / (m : Real) ^ 4) :=
          mul_le_mul_of_nonneg_right hNReal (by positivity)
        _ = 12 / (m : Real) ^ 2 := by field_simp
    _ = 24 / (m : Real) ^ 2 := by ring


end
end StatMech.Universality
