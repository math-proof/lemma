/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointEscape.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part2


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem endpointFarEscapeWitness_weight_le
    (m t : Nat) (start target : Int) (hm : 0 < m) (ht : t ≤ m * m) :
    Nat.card (IsingEndpointFarEscapeWitnessFamily m t start target) /
        (4 : Real) ^ t ≤
      468 / (m : Real) ^ 2 := by
  have hcard : Nat.card (IsingEndpointFarEscapeWitnessFamily
      m t start target) =
      ∑ j : Fin (t + 1),
        Nat.card (IsingLineFarFirstBoundaryFamily m j) *
          Nat.card (VerticalChoicePathFamily j start target) *
            4 ^ (t - j) := by
    letI (j : Fin (t + 1)) :
        Fintype (IsingLineFarFirstBoundaryFamily m j) := Fintype.ofFinite _
    letI (j : Fin (t + 1)) :
        Fintype (VerticalChoicePathFamily j start target) := Fintype.ofFinite _
    letI (j : Fin (t + 1)) :
        Fintype {tail : List (Bool × Bool) // tail.length = t - j} :=
      (List.finite_length_eq (Bool × Bool) (t - j)).fintype
    change Nat.card (Σ j : Fin (t + 1),
      IsingLineFarFirstBoundaryFamily m j ×
        VerticalChoicePathFamily j start target ×
          {tail : List (Bool × Bool) // tail.length = t - j}) = _
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro j hj
    have htail : Nat.card
        {tail : List (Bool × Bool) // tail.length = t - (j : Nat)} =
        4 ^ (t - (j : Nat)) := by
      change Nat.card (List.Vector (Bool × Bool) (t - (j : Nat))) =
        4 ^ (t - (j : Nat))
      rw [Nat.card_congr
          (Equiv.vectorEquivFin (Bool × Bool) (t - (j : Nat))),
        Nat.card_eq_fintype_card, Fintype.card_fun]
      norm_num
    calc
      Nat.card (IsingLineFarFirstBoundaryFamily m j ×
          VerticalChoicePathFamily j start target ×
            {tail : List (Bool × Bool) // tail.length = t - j}) =
        Nat.card (IsingLineFarFirstBoundaryFamily m j) *
          (Nat.card (VerticalChoicePathFamily j start target) *
            Nat.card {tail : List (Bool × Bool) // tail.length = t - j}) := by
          rw [Nat.card_prod, Nat.card_prod]
      _ = _ := by rw [htail]; ring
  have hmass :
      Nat.card (IsingEndpointFarEscapeWitnessFamily m t start target) /
          (4 : Real) ^ t =
        ∑ j ∈ Finset.range (t + 1),
          (Nat.card (VerticalChoicePathFamily j start target) /
              (2 : Real) ^ j) *
            (Nat.card (IsingLineFarFirstBoundaryFamily m j) /
              (2 : Real) ^ j) := by
    rw [hcard]
    push_cast
    rw [Fin.sum_univ_eq_sum_range
      (fun j : Nat =>
        (Nat.card (IsingLineFarFirstBoundaryFamily m j) : Real) *
          (Nat.card (VerticalChoicePathFamily j start target) : Real) *
            (4 : Real) ^ (t - j)) (t + 1)]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have hjt : j ≤ t := by
      have := Finset.mem_range.mp hj
      omega
    have hfour : (4 : Real) ^ t =
        (4 : Real) ^ j * (4 : Real) ^ (t - j) := by
      calc
        (4 : Real) ^ t = (4 : Real) ^ (j + (t - j)) := by
          congr 1
          omega
        _ = _ := pow_add _ _ _
    have htwo : (4 : Real) ^ j =
        (2 : Real) ^ j * (2 : Real) ^ j := by
      rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
    rw [hfour, htwo]
    field_simp
  rw [hmass]
  calc
    _ ≤ ∑ j ∈ Finset.range (t + 1),
        (2 / Real.sqrt (j + 1 : Real)) *
          (Nat.card (IsingLineFarFirstBoundaryFamily m j) /
            (2 : Real) ^ j) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right
      · rw [← isingLineBinomialKernel_eq_natCard_verticalChoicePath_div]
        let K := isingLineBinomialKernel j start target
        have hK0 : 0 ≤ K := isingLineBinomialKernel_nonneg _ _ _
        have hrad : 0 ≤ 2 / (j + 1 : Real) := by positivity
        have hK : K ≤ Real.sqrt (2 / (j + 1 : Real)) := by
          rw [Real.le_sqrt hK0 hrad]
          exact isingLineBinomialKernel_sq_le j start target
        calc
          K ≤ Real.sqrt (2 / (j + 1 : Real)) := hK
          _ ≤ 2 / Real.sqrt (j + 1 : Real) := by
            rw [Real.sqrt_div (by positivity)]
            apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
            have hsqrt2 : Real.sqrt (2 : Real) ≤ 2 := by
              rw [Real.sqrt_le_iff]
              norm_num
            exact hsqrt2
      · positivity
    _ ≤ 468 / (m : Real) ^ 2 :=
      endpointKernel_farFirstBoundary_sum_le m t hm ht

theorem endpointFarEscapeWitness_diffusive_weight_le
    (rho m : Nat) (start target : Int) (hρ : 0 < rho) (hm : rho ≤ m) :
    Nat.card (IsingEndpointFarEscapeWitnessFamily
          m (rho * rho) start target) /
        (4 : Real) ^ (rho * rho) ≤
      468 / (rho : Real) ^ 2 := by
  have hm0 : 0 < m := lt_of_lt_of_le hρ hm
  have ht : rho * rho ≤ m * m := Nat.mul_self_le_mul_self hm
  have h := endpointFarEscapeWitness_weight_le
    m (rho * rho) start target hm0 ht
  have hrm : (rho : Real) ^ 2 ≤ (m : Real) ^ 2 := by
    exact_mod_cast (show rho ^ 2 ≤ m ^ 2 by
      simpa [pow_two] using ht)
  calc
    _ ≤ 468 / (m : Real) ^ 2 := h
    _ ≤ 468 / (rho : Real) ^ 2 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hrm

end
end StatMech.Universality
