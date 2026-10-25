/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part6


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem sqrt_ballot_le_four_div_sqrt (k : Nat) :
    2 * Real.sqrt (2 / (k + 1 : Real)) ≤
      4 / Real.sqrt (k + 1 : Real) := by
  have hs : 0 < Real.sqrt (k + 1 : Real) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt (2 : Real) ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  rw [Real.sqrt_div (by positivity)]
  rw [show 2 * (Real.sqrt 2 / Real.sqrt (k + 1 : Real)) =
      (2 * Real.sqrt 2) / Real.sqrt (k + 1 : Real) by ring]
  exact (div_le_div_iff_of_pos_right hs).2 (by nlinarith)


theorem transverseRaceWitness_diffusive_weight_le
    (rho m : Nat) (level : Int) (hρ : 0 < rho) (hm : rho ≤ m) :
    Nat.card (IsingTransverseRaceWitnessFamily m (rho * rho) level) /
        (4 : Real) ^ (rho * rho) ≤ 16 / (rho : Real) := by
  let T := rho * rho
  let b : Nat → Real := fun j =>
    Nat.card (IsingLineFirstBoundaryFamily m j) / (2 : Real) ^ j
  have hcard : Nat.card (IsingTransverseRaceWitnessFamily m T level) =
      ∑ j : Fin (T + 1),
        Nat.card (IsingHorizontalNoHitFamily j (level - 1) level) *
          Nat.card (IsingLineFirstBoundaryFamily m j) * 4 ^ (T - j) := by
    letI (j : Fin (T + 1)) :
        Fintype (IsingHorizontalNoHitFamily j (level - 1) level) :=
      Fintype.ofFinite _
    letI (j : Fin (T + 1)) :
        Fintype (IsingLineFirstBoundaryFamily m j) := Fintype.ofFinite _
    letI (j : Fin (T + 1)) :
        Fintype {tail : List (Bool × Bool) // tail.length = T - j} :=
      (List.finite_length_eq (Bool × Bool) (T - j)).fintype
    change Nat.card (Σ j : Fin (T + 1),
      IsingHorizontalNoHitFamily j (level - 1) level ×
        IsingLineFirstBoundaryFamily m j ×
          {tail : List (Bool × Bool) // tail.length = T - j}) = _
    rw [Nat.card_sigma]
    apply Finset.sum_congr rfl
    intro j hj
    have htail : Nat.card
        {tail : List (Bool × Bool) // tail.length = T - (j : Nat)} =
        4 ^ (T - (j : Nat)) := by
      change Nat.card (List.Vector (Bool × Bool) (T - (j : Nat))) =
        4 ^ (T - (j : Nat))
      rw [Nat.card_congr
          (Equiv.vectorEquivFin (Bool × Bool) (T - (j : Nat))),
        Nat.card_eq_fintype_card, Fintype.card_fun]
      norm_num
    calc
      Nat.card (IsingHorizontalNoHitFamily j (level - 1) level ×
          IsingLineFirstBoundaryFamily m j ×
            {tail : List (Bool × Bool) // tail.length = T - j}) =
        Nat.card (IsingHorizontalNoHitFamily j (level - 1) level) *
          (Nat.card (IsingLineFirstBoundaryFamily m j) *
            Nat.card {tail : List (Bool × Bool) // tail.length = T - j}) := by
          rw [Nat.card_prod, Nat.card_prod]
      _ = _ := by rw [htail]; ring
  have hmass :
      Nat.card (IsingTransverseRaceWitnessFamily m T level) /
          (4 : Real) ^ T =
        ∑ j ∈ Finset.range (T + 1),
          (Nat.card (IsingHorizontalNoHitFamily j (level - 1) level) /
              (2 : Real) ^ j) * b j := by
    rw [hcard]
    push_cast
    rw [Fin.sum_univ_eq_sum_range
      (fun j : Nat =>
        (Nat.card (IsingHorizontalNoHitFamily j (level - 1) level) : Real) *
          (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
            (4 : Real) ^ (T - j)) (T + 1)]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    have hjT : j ≤ T := by
      have := Finset.mem_range.mp hj
      omega
    have hfour : (4 : Real) ^ T =
        (4 : Real) ^ j * (4 : Real) ^ (T - j) := by
      calc
        (4 : Real) ^ T = (4 : Real) ^ (j + (T - j)) := by
          congr 1
          omega
        _ = _ := pow_add _ _ _
    have htwo : (4 : Real) ^ j = (2 : Real) ^ j * (2 : Real) ^ j := by
      rw [show (4 : Real) = 2 * 2 by norm_num, mul_pow]
    dsimp [b]
    rw [hfour, htwo]
    field_simp
  rw [show rho * rho = T by rfl, hmass]
  have hpoint (j : Nat) :
      Nat.card (IsingHorizontalNoHitFamily j (level - 1) level) /
          (2 : Real) ^ j ≤ 4 / Real.sqrt (j + 1 : Real) := by
    exact le_trans (horizontalNoHit_weight_le_sqrt j level)
      (sqrt_ballot_le_four_div_sqrt j)
  calc
    (∑ j ∈ Finset.range (T + 1),
      (Nat.card (IsingHorizontalNoHitFamily j (level - 1) level) /
        (2 : Real) ^ j) * b j) ≤
        ∑ j ∈ Finset.range (T + 1),
          (4 / Real.sqrt (j + 1 : Real)) * b j := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_right (hpoint j)
      dsimp [b]
      positivity
    _ ≤ 16 / (rho : Real) := by
      apply ballotWeight_firstHit_sum_le rho T b hρ
      · dsimp [T]
        exact le_rfl
      · intro k hk
        have hfirst := lineFirstBoundary_partial_weight_le m k (lt_of_lt_of_le hρ hm)
        have hmReal : (rho : Real) ^ 2 ≤ (m : Real) ^ 2 := by
          nlinarith [show (rho : Real) ≤ (m : Real) by exact_mod_cast hm]
        calc
          (∑ j ∈ Finset.range (k + 1), b j) ≤
              (k : Real) / (m : Real) ^ 2 := by
            simpa [b] using hfirst
          _ ≤ (k + 1 : Real) / (rho : Real) ^ 2 := by
            apply div_le_div₀
            · positivity
            · norm_num
            · positivity
            · exact hmReal


end
end StatMech.Universality
