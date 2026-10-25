/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCharacter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWPhaseLoops
import Theorem.StatisticalMechanics.Code.Onsager.TorusSpinSectors.Part3
import Def.StatisticalMechanics.Code.Onsager.SpinCharacter.Part2


namespace StatMech.Onsager

open BigOperators StatMech.Ising

theorem ons_spinCharacterSum_eq_sector_sum (L : ℕ) [Fact (2 < L)]
    (x : ℝ) (a b : Fin 2) :
    ons_spinCharacterSum L x a b =
      ∑ h : Fin 2 × Fin 2,
        ons_spinCharacter a b h * ons_sectorWeight L x h := by
  unfold ons_spinCharacterSum ons_sectorWeight
  calc
    (∑ F ∈ evenSubgraphs (onsTorusGraph L),
        ons_spinCharacter a b (ons_evenHomology L F) * x ^ F.card) =
        ∑ h : Fin 2 × Fin 2,
          ∑ F ∈ evenSubgraphs (onsTorusGraph L) with ons_evenHomology L F = h,
            ons_spinCharacter a b (ons_evenHomology L F) * x ^ F.card :=
      (Finset.sum_fiberwise
        (evenSubgraphs (onsTorusGraph L)) (ons_evenHomology L)
        (fun F => ons_spinCharacter a b (ons_evenHomology L F) * x ^ F.card)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F hF
      rw [(Finset.mem_filter.mp hF).2]

theorem ons_spinCharacterSum_zero_zero (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    ons_spinCharacterSum L x 0 0 = ons_spin11 L x := by
  rw [ons_spinCharacterSum_eq_sector_sum]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, ons_spinCharacter,
    ons_spin11, ons_sector00, ons_sector10, ons_sector01, ons_sector11]
  ring

theorem ons_spinCharacterSum_one_zero (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    ons_spinCharacterSum L x 1 0 = ons_spin01 L x := by
  rw [ons_spinCharacterSum_eq_sector_sum]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, ons_spinCharacter,
    ons_spin01, ons_sector00, ons_sector10, ons_sector01, ons_sector11]
  ring

theorem ons_spinCharacterSum_zero_one (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    ons_spinCharacterSum L x 0 1 = ons_spin10 L x := by
  rw [ons_spinCharacterSum_eq_sector_sum]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, ons_spinCharacter,
    ons_spin10, ons_sector00, ons_sector10, ons_sector01, ons_sector11]
  ring

theorem ons_spinCharacterSum_one_one (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    ons_spinCharacterSum L x 1 1 = ons_spin00 L x := by
  rw [ons_spinCharacterSum_eq_sector_sum]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, ons_spinCharacter,
    ons_spin00, ons_sector00, ons_sector10, ons_sector01, ons_sector11]
  ring

end StatMech.Onsager
