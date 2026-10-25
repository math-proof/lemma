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
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part6


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem orderedFarHorizontalEndpoint_weight_eq_sum
    (m R t : Nat) (mark target : IsingLineBox R)
    (startY targetY : Int) :
    Nat.card (IsingOrderedFarHorizontalEndpointFamily
        m R t mark target startY targetY) / (4 : Real) ^ t =
      ∑ k : Fin (t + 1), ∑ j : Fin k,
        (Nat.card (IsingLineFarFirstBoundaryFamily m j) /
          (2 : Real) ^ (j : Nat)) *
        (Nat.card (IsingLineFirstEndpointFamily R (k - j) mark target) /
          (2 : Real) ^ ((k : Nat) - (j : Nat))) *
        (Nat.card (VerticalChoicePathFamily k startY targetY) /
          (2 : Real) ^ (k : Nat)) := by
  letI (k : Fin (t + 1)) : Fintype (Fin k) := inferInstance
  letI (k : Fin (t + 1)) (j : Fin k) :
      Fintype (IsingLineFarFirstBoundaryFamily m j) := Fintype.ofFinite _
  letI (k : Fin (t + 1)) (j : Fin k) :
      Fintype (IsingLineFirstEndpointFamily R (k - j) mark target) :=
    Fintype.ofFinite _
  letI (k : Fin (t + 1)) :
      Fintype (VerticalChoicePathFamily k startY targetY) := Fintype.ofFinite _
  letI (k : Fin (t + 1)) :
      Fintype {tail : List (Bool × Bool) // tail.length = t - k} :=
    (List.finite_length_eq (Bool × Bool) (t - k)).fintype
  have hcard : Nat.card (IsingOrderedFarHorizontalEndpointFamily
      m R t mark target startY targetY) =
      ∑ k : Fin (t + 1), ∑ j : Fin k,
        Nat.card (IsingLineFarFirstBoundaryFamily m j) *
        Nat.card (IsingLineFirstEndpointFamily R (k - j) mark target) *
        Nat.card (VerticalChoicePathFamily k startY targetY) *
        4 ^ (t - (k : Nat)) := by
    unfold IsingOrderedFarHorizontalEndpointFamily
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
  rw [hcard]
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

end
end StatMech.Universality
