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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part16


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem lineFirstEndpointRightToNoHit_injective
    (n k : Nat) (start target : IsingLineBox n)
    (hk : 0 < k) (htarget : target.1 = n) :
    Function.Injective
      (lineFirstEndpointRightToNoHit n k start target hk htarget) := by
  intro a b hab
  have hword := congrArg
    (fun z : IsingHorizontalNoHitEndpointFamily (k - 1) n
      (start.1 : Int) => z.1.1) hab
  change a.1.dropLast.reverse.map (!.) =
    b.1.dropLast.reverse.map (!.) at hword
  have hnotInjective : Function.Injective (fun b : Bool => !b) := by
    intro x y h
    cases x <;> cases y <;> simp at h ⊢
  have hreverse : a.1.dropLast.reverse = b.1.dropLast.reverse :=
    (Function.Injective.list_map hnotInjective) hword
  have hdrop : a.1.dropLast = b.1.dropLast :=
    List.reverse_injective hreverse
  apply Subtype.ext
  rw [(lineFirstEndpoint_right_dropLast n k start target a hk htarget).2,
    (lineFirstEndpoint_right_dropLast n k start target b hk htarget).2,
    hdrop]


theorem lineFirstEndpoint_boundary_weight_le
    (n k : Nat) (start target : IsingLineBox n)
    (hk : 0 < k) (htarget : isingLineBoxBoundary n target) :
    Nat.card (IsingLineFirstEndpointFamily n k start target) /
        (2 : Real) ^ k <= 2 / (k : Real) := by
  rcases htarget with hleft | hright
  · have hcard : Nat.card (IsingLineFirstEndpointFamily n k start target) <=
        Nat.card (IsingHorizontalNoHitEndpointFamily
          (k - 1) 0 (-(start.1 : Int))) :=
      Nat.card_le_card_of_injective
        (lineFirstEndpointLeftToNoHit n k start target hk hleft)
        (lineFirstEndpointLeftToNoHit_injective n k start target hk hleft)
    have hballot := horizontalNoHitEndpoint_weight_le
      (k - 1) 0 (-(start.1 : Int))
    have hpow : (2 : Real) ^ k = 2 * (2 : Real) ^ (k - 1) := by
      calc
        _ = (2 : Real) ^ ((k - 1) + 1) := by congr 1; omega
        _ = _ := by rw [pow_add]; norm_num; ring
    calc
      _ <= Nat.card (IsingHorizontalNoHitEndpointFamily
          (k - 1) 0 (-(start.1 : Int))) / (2 : Real) ^ k := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
      _ = (1 / 2 : Real) *
          (Nat.card (IsingHorizontalNoHitEndpointFamily
            (k - 1) 0 (-(start.1 : Int))) / (2 : Real) ^ (k - 1)) := by
        rw [hpow]
        ring
      _ <= (1 / 2 : Real) * (4 / (k : Real)) := by
        apply mul_le_mul_of_nonneg_left
        · have hkCast : (((k - 1 : Nat) : Real) + 1) = (k : Real) := by
            exact_mod_cast (show k - 1 + 1 = k by omega)
          rw [hkCast] at hballot
          exact hballot
        · norm_num
      _ = 2 / (k : Real) := by ring
  · have hcard : Nat.card (IsingLineFirstEndpointFamily n k start target) <=
        Nat.card (IsingHorizontalNoHitEndpointFamily
          (k - 1) n (start.1 : Int)) :=
      Nat.card_le_card_of_injective
        (lineFirstEndpointRightToNoHit n k start target hk hright)
        (lineFirstEndpointRightToNoHit_injective n k start target hk hright)
    have hballot := horizontalNoHitEndpoint_weight_le
      (k - 1) n (start.1 : Int)
    have hpow : (2 : Real) ^ k = 2 * (2 : Real) ^ (k - 1) := by
      calc
        _ = (2 : Real) ^ ((k - 1) + 1) := by congr 1; omega
        _ = _ := by rw [pow_add]; norm_num; ring
    calc
      _ <= Nat.card (IsingHorizontalNoHitEndpointFamily
          (k - 1) n (start.1 : Int)) / (2 : Real) ^ k := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast hcard
      _ = (1 / 2 : Real) *
          (Nat.card (IsingHorizontalNoHitEndpointFamily
            (k - 1) n (start.1 : Int)) / (2 : Real) ^ (k - 1)) := by
        rw [hpow]
        ring
      _ <= (1 / 2 : Real) * (4 / (k : Real)) := by
        apply mul_le_mul_of_nonneg_left
        · have hkCast : (((k - 1 : Nat) : Real) + 1) = (k : Real) := by
            exact_mod_cast (show k - 1 + 1 = k by omega)
          rw [hkCast] at hballot
          exact hballot
        · norm_num
      _ = 2 / (k : Real) := by ring


end
end StatMech.Universality
