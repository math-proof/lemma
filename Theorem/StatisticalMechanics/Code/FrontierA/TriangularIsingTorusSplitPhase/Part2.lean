/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitEmbedding.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePrimitive.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSplitPhase.Part2


namespace StatMech.FrontierA

open SimpleGraph


theorem triangularSplit_entry_phase
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    (a b : Fin 6)
    (hadj : (triangularTorusDirectionRank a).val + 1 =
          (triangularTorusDirectionRank b).val ∨
        (triangularTorusDirectionRank b).val + 1 =
          (triangularTorusDirectionRank a).val) :
    triangularKacWardTurnMatrix rho (triangularTorusDirectionReverse a)
        (triangularTorusSplitInternalDirection a b) =
      (if (triangularTorusDirectionRank a).val <
          (triangularTorusDirectionRank b).val then
        -Complex.I *
          (rho ^ triangularTorusDirectionSignedAngle a)⁻¹
      else
        Complex.I *
          (rho ^ triangularTorusDirectionSignedAngle a)⁻¹) *
        triangularTorusSplitInternalGauge rho a b := by
  have hrho0 := triangularTorusTurnRoot_ne_zero rho hrho
  have hrho8 := triangularTorusTurnRoot_pow_eight rho hrho
  have hrho12 : rho ^ 12 = -Complex.I := by
    calc
      rho ^ 12 = rho ^ 8 * rho ^ 4 := by ring
      _ = -Complex.I := by rw [hrho8, hrho]; ring
  have hrho16 : rho ^ 16 = 1 := by rw [show rho ^ 16 = (rho ^ 8) ^ 2 by ring, hrho8]; norm_num
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionRank,
      triangularTorusDirectionReverse,
      triangularTorusSplitInternalDirection,
      triangularTorusSplitIncreasingDirection,
      triangularTorusSplitInternalGauge,
      triangularTorusSplitIncreasingGaugeExponent,
      triangularTorusSplitDecreasingGaugeExponent,
      triangularTorusDirectionSignedAngle,
      triangularKacWardTurnMatrix] at hadj ⊢ <;>
    field_simp <;> try simp [hrho, hrho8, hrho12, hrho16, Complex.I_sq]

theorem triangularSplit_exit_phase
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    (a b : Fin 6)
    (hadj : (triangularTorusDirectionRank a).val + 1 =
          (triangularTorusDirectionRank b).val ∨
        (triangularTorusDirectionRank b).val + 1 =
          (triangularTorusDirectionRank a).val) :
    triangularKacWardTurnMatrix rho
        (triangularTorusSplitInternalDirection a b) b =
      (triangularTorusSplitInternalGauge rho a b)⁻¹ *
        rho ^ triangularTorusDirectionSignedAngle b := by
  have hrho0 := triangularTorusTurnRoot_ne_zero rho hrho
  have hrho8 := triangularTorusTurnRoot_pow_eight rho hrho
  have hrho12 : rho ^ 12 = -Complex.I := by
    calc
      rho ^ 12 = rho ^ 8 * rho ^ 4 := by ring
      _ = -Complex.I := by rw [hrho8, hrho]; ring
  have hrho16 : rho ^ 16 = 1 := by rw [show rho ^ 16 = (rho ^ 8) ^ 2 by ring, hrho8]; norm_num
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionRank,
      triangularTorusSplitInternalDirection,
      triangularTorusSplitIncreasingDirection,
      triangularTorusSplitInternalGauge,
      triangularTorusSplitIncreasingGaugeExponent,
      triangularTorusSplitDecreasingGaugeExponent,
      triangularTorusDirectionReverse,
      triangularTorusDirectionSignedAngle,
      triangularKacWardTurnMatrix] at hadj ⊢ <;>
    field_simp <;> try simp [hrho, hrho8, hrho12, hrho16, Complex.I_sq]

theorem triangularSplit_internal_phase
    (rho : Complex) (hrho : rho ^ 4 = Complex.I)
    (a b c : Fin 6)
    (hab : (triangularTorusDirectionRank a).val + 1 =
          (triangularTorusDirectionRank b).val ∨
        (triangularTorusDirectionRank b).val + 1 =
          (triangularTorusDirectionRank a).val)
    (hbc : (triangularTorusDirectionRank b).val + 1 =
          (triangularTorusDirectionRank c).val ∨
        (triangularTorusDirectionRank c).val + 1 =
          (triangularTorusDirectionRank b).val)
    (hmono : ((triangularTorusDirectionRank a).val <
          (triangularTorusDirectionRank b).val ∧
        (triangularTorusDirectionRank b).val <
          (triangularTorusDirectionRank c).val) ∨
      ((triangularTorusDirectionRank b).val <
          (triangularTorusDirectionRank a).val ∧
        (triangularTorusDirectionRank c).val <
          (triangularTorusDirectionRank b).val)) :
    triangularKacWardTurnMatrix rho
        (triangularTorusSplitInternalDirection a b)
        (triangularTorusSplitInternalDirection b c) =
      (triangularTorusSplitInternalGauge rho a b)⁻¹ *
        triangularTorusSplitInternalGauge rho b c := by
  have hrho0 := triangularTorusTurnRoot_ne_zero rho hrho
  have hrho8 := triangularTorusTurnRoot_pow_eight rho hrho
  have hrho12 : rho ^ 12 = -Complex.I := by
    calc
      rho ^ 12 = rho ^ 8 * rho ^ 4 := by ring
      _ = -Complex.I := by rw [hrho8, hrho]; ring
  have hrho16 : rho ^ 16 = 1 := by rw [show rho ^ 16 = (rho ^ 8) ^ 2 by ring, hrho8]; norm_num
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [triangularTorusDirectionRank,
      triangularTorusSplitInternalDirection,
      triangularTorusSplitIncreasingDirection,
      triangularTorusSplitInternalGauge,
      triangularTorusSplitIncreasingGaugeExponent,
      triangularTorusSplitDecreasingGaugeExponent,
      triangularTorusDirectionReverse,
      triangularTorusDirectionSignedAngle,
      triangularKacWardTurnMatrix] at hab hbc hmono ⊢ <;>
    field_simp <;> try simp [hrho, hrho8, hrho12, hrho16, Complex.I_sq]

end StatMech.FrontierA
