/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part12


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem lineFirstBoundary_partial_weight_le
    (m K : Nat) (hm : 0 < m) :
    (∑ j ∈ Finset.range (K + 1),
      (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) /
        (2 : Real) ^ j) ≤ (K : Real) / (m : Real) ^ 2 := by
  have hcard : Nat.card (IsingLineFirstBoundaryExtension m K) ≤
      Nat.card (IsingLineBoundaryStringFamily m K) :=
    Nat.card_le_card_of_injective (lineFirstBoundaryExtend m K)
      (lineFirstBoundaryExtend_injective m K)
  have hext : Nat.card (IsingLineFirstBoundaryExtension m K) =
      ∑ j : Fin (K + 1),
        Nat.card (IsingLineFirstBoundaryFamily m j) * 2 ^ (K - j) := by
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
  have hboundary : Nat.card (IsingLineBoundaryStringFamily m K) =
      Nat.card (IsingLineChoicePathFamily (2 * m) K
          ⟨m, by omega⟩ ⟨0, by omega⟩) +
        Nat.card (IsingLineChoicePathFamily (2 * m) K
          ⟨m, by omega⟩ ⟨2 * m, by omega⟩) := by
    rw [Nat.card_congr (lineBoundaryStringEquivSum m K hm), Nat.card_sum]
  have hweightedNat :
      (∑ j : Fin (K + 1),
        Nat.card (IsingLineFirstBoundaryFamily m j) * 2 ^ (K - j)) ≤
          Nat.card (IsingLineBoundaryStringFamily m K) := by
    rw [← hext]
    exact hcard
  have hweightedReal :
      (∑ j : Fin (K + 1),
        (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
          (2 : Real) ^ (K - j)) ≤
          (Nat.card (IsingLineBoundaryStringFamily m K) : Real) := by
    exact_mod_cast hweightedNat
  rw [Fin.sum_univ_eq_sum_range
    (fun j : Nat => (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
      (2 : Real) ^ (K - j)) (K + 1)] at hweightedReal
  have htwo : 0 < (2 : Real) ^ K := by positivity
  have hdiv := div_le_div_of_nonneg_right hweightedReal htwo.le
  have hcardReal :
      (∑ j ∈ Finset.range (K + 1),
        (Nat.card (IsingLineFirstBoundaryFamily m j) : Real) /
          (2 : Real) ^ j) ≤
        ((Nat.card (IsingLineBoundaryStringFamily m K) : Real) /
          (2 : Real) ^ K) := by
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
          _ = ((Nat.card (IsingLineFirstBoundaryFamily m j) : Real) *
              (2 : Real) ^ (K - j)) / (2 : Real) ^ K := by
            rw [hpow]
      _ ≤ _ := hdiv
  calc
    _ ≤ (Nat.card (IsingLineBoundaryStringFamily m K) : Real) /
          (2 : Real) ^ K := hcardReal
    _ = isingLineStoppedKernel (2 * m) K ⟨m, by omega⟩ ⟨0, by omega⟩ +
        isingLineStoppedKernel (2 * m) K ⟨m, by omega⟩
          ⟨2 * m, by omega⟩ := by
      rw [hboundary]
      push_cast
      rw [add_div]
      rw [isingLineStoppedKernel_eq_natCard_choicePath_div,
        isingLineStoppedKernel_eq_natCard_choicePath_div]
    _ ≤ (K : Real) / (m : Real) ^ 2 :=
      isingLineStoppedKernel_center_boundary_le m K hm


end
end StatMech.Universality
