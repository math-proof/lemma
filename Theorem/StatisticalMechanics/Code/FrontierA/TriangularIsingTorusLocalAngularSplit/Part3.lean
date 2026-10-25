/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusLocalAngularSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplit.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusAngularSplit
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part5
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusLocalAngularSplit.Part3


namespace StatMech.FrontierA

open SimpleGraph


theorem triangularTorusGraphDartDirection_symm
    (L : Nat) [Fact (2 < L)]
    (d : (triangularTorusGraph L).Dart) :
    triangularTorusGraphDartDirection L d.symm =
      triangularTorusDirectionReverse
        (triangularTorusGraphDartDirection L d) := by
  let a := (triangularTorusDartEquiv L).symm d
  have hd : triangularTorusDartEquiv L a = d :=
    (triangularTorusDartEquiv L).apply_symm_apply d
  unfold triangularTorusGraphDartDirection
  rw [← hd, ← triangularTorusDartEquiv_reverse]
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl


theorem triangularKacWardTurnMatrix_eq_localRoots_of_rank_lt
    (rho : Complex) (hrho : rho ^ 4 = Complex.I) (a b : Fin 6)
    (hrank : (triangularTorusDirectionRank
        (triangularTorusDirectionReverse a)).val <
      (triangularTorusDirectionRank b).val) :
    triangularKacWardTurnMatrix rho a b =
      -Complex.I *
        (rho ^ triangularTorusDirectionSignedAngle
          (triangularTorusDirectionReverse a))⁻¹ *
        rho ^ triangularTorusDirectionSignedAngle b := by
  have hrho0 := triangularTorusTurnRoot_ne_zero rho hrho
  have hrho8 := triangularTorusTurnRoot_pow_eight rho hrho
  have hrho12 : rho ^ 12 = -Complex.I := by
    calc
      rho ^ 12 = rho ^ 8 * rho ^ 4 := by ring
      _ = -Complex.I := by rw [hrho8, hrho]; ring
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionRank,
      triangularTorusDirectionReverse,
      triangularTorusDirectionSignedAngle,
      triangularKacWardTurnMatrix] at hrank ⊢ <;>
    field_simp <;>
    simp [hrho]


theorem triangularKacWardTurnMatrix_eq_localRoots_of_rank_gt
    (rho : Complex) (hrho : rho ^ 4 = Complex.I) (a b : Fin 6)
    (hrank : (triangularTorusDirectionRank b).val <
      (triangularTorusDirectionRank
        (triangularTorusDirectionReverse a)).val) :
    triangularKacWardTurnMatrix rho a b =
      Complex.I *
        (rho ^ triangularTorusDirectionSignedAngle
          (triangularTorusDirectionReverse a))⁻¹ *
        rho ^ triangularTorusDirectionSignedAngle b := by
  have hrho0 := triangularTorusTurnRoot_ne_zero rho hrho
  have hrho8 := triangularTorusTurnRoot_pow_eight rho hrho
  have hrho12 : rho ^ 12 = -Complex.I := by
    calc
      rho ^ 12 = rho ^ 8 * rho ^ 4 := by ring
      _ = -Complex.I := by rw [hrho8, hrho]; ring
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionRank,
      triangularTorusDirectionReverse,
      triangularTorusDirectionSignedAngle,
      triangularKacWardTurnMatrix] at hrank ⊢ <;>
    field_simp <;>
    simp [hrho, hrho12]


end StatMech.FrontierA
