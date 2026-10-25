/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalBallot.Part5
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFourthMoment
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part2


namespace StatMech.Universality

open Finset

noncomputable section

theorem endpointTransverseRaceWitness_weight_le
    (m t : Nat) (level target : Int) (hm : 0 < m) (ht : t ≤ m * m) :
    Nat.card (IsingEndpointTransverseRaceWitnessFamily m t level target) /
        (4 : Real) ^ t ≤
      24 / (m : Real) ^ 2 := by
  have hcard :
      Nat.card (IsingEndpointTransverseRaceWitnessFamily m t level target) =
        ∑ j : Fin (t + 1),
          Nat.card (IsingHorizontalNoHitEndpointFamily j level target) *
            Nat.card (IsingLineFirstBoundaryFamily m j) * 4 ^ (t - j) := by
    letI (j : Fin (t + 1)) :
        Fintype (IsingHorizontalNoHitEndpointFamily j level target) :=
      Fintype.ofFinite _
    letI (j : Fin (t + 1)) :
        Fintype (IsingLineFirstBoundaryFamily m j) := Fintype.ofFinite _
    letI (j : Fin (t + 1)) :
        Fintype {tail : List (Bool × Bool) // tail.length = t - j} :=
      (List.finite_length_eq (Bool × Bool) (t - j)).fintype
    change Nat.card (Σ j : Fin (t + 1),
      IsingHorizontalNoHitEndpointFamily j level target ×
        IsingLineFirstBoundaryFamily m j ×
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
      Nat.card (IsingHorizontalNoHitEndpointFamily j level target ×
          IsingLineFirstBoundaryFamily m j ×
            {tail : List (Bool × Bool) // tail.length = t - j}) =
        Nat.card (IsingHorizontalNoHitEndpointFamily j level target) *
          (Nat.card (IsingLineFirstBoundaryFamily m j) *
            Nat.card {tail : List (Bool × Bool) // tail.length = t - j}) := by
          rw [Nat.card_prod, Nat.card_prod]
      _ = _ := by rw [htail]; ring
  have hmass :
      Nat.card (IsingEndpointTransverseRaceWitnessFamily m t level target) /
          (4 : Real) ^ t =
        ∑ j ∈ Finset.range (t + 1),
          (Nat.card (IsingHorizontalNoHitEndpointFamily j level target) /
              (2 : Real) ^ j) *
            (Nat.card (IsingLineFirstBoundaryFamily m j) /
              (2 : Real) ^ j) := by
    rw [hcard]
    push_cast
    rw [Fin.sum_univ_eq_sum_range
      (fun j : Nat =>
        (Nat.card (IsingHorizontalNoHitEndpointFamily j level target) : Real) *
          (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
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
        (4 / (j + 1 : Real)) *
          (Nat.card (IsingLineFirstBoundaryFamily m j) /
            (2 : Real) ^ j) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right
        (horizontalNoHitEndpoint_weight_le j level target)
      positivity
    _ ≤ 24 / (m : Real) ^ 2 :=
      endpointBallot_firstBoundary_sum_le m t hm ht


theorem endpointTransverseRaceWitness_diffusive_weight_le
    (rho m : Nat) (level target : Int) (hρ : 0 < rho) (hm : rho ≤ m) :
    Nat.card (IsingEndpointTransverseRaceWitnessFamily
          m (rho * rho) level target) /
        (4 : Real) ^ (rho * rho) ≤
      24 / (rho : Real) ^ 2 := by
  have hm0 : 0 < m := lt_of_lt_of_le hρ hm
  have ht : rho * rho ≤ m * m := Nat.mul_self_le_mul_self hm
  have h := endpointTransverseRaceWitness_weight_le
    m (rho * rho) level target hm0 ht
  have hrm : (rho : Real) ^ 2 ≤ (m : Real) ^ 2 := by
    exact_mod_cast (show rho ^ 2 ≤ m ^ 2 by
      simpa [pow_two] using ht)
  calc
    _ ≤ 24 / (m : Real) ^ 2 := h
    _ ≤ 24 / (rho : Real) ^ 2 := by
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hrm

end
end StatMech.Universality
