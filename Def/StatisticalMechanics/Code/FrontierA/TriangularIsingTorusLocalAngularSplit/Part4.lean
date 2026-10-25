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
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusLocalAngularSplit.Part3


namespace StatMech.FrontierA

open SimpleGraph


noncomputable def triangularTorusLocalAngularData
    (L : Nat) [Fact (2 < L)] (rho : Complex)
    (hrho : rho ^ 4 = Complex.I) :
    KWLocalAngularData (triangularTorusGraph L) where
  order := triangularTorusLocalPortOrder L
  root := triangularTorusLocalPortRoot L rho
  phase := triangularTorusGraphPhase L rho 1 1
  phase_eq_portRoots_of_rank_lt d e _hde hrank := by
    rw [triangularTorusGraphPhase_one_one_apply]
    unfold triangularTorusLocalPortRoot
    simp only [kwDartOfPort_portOfDart]
    rw [triangularTorusGraphDartDirection_symm]
    apply triangularKacWardTurnMatrix_eq_localRoots_of_rank_lt rho hrho
    rw [triangularTorusLocalPortOrder_rank,
      triangularTorusLocalPortOrder_rank] at hrank
    simp only [kwDartOfPort_portOfDart,
      triangularTorusGraphDartDirection_symm] at hrank
    exact hrank
  phase_eq_portRoots_of_rank_gt d e _hde hrank := by
    rw [triangularTorusGraphPhase_one_one_apply]
    unfold triangularTorusLocalPortRoot
    simp only [kwDartOfPort_portOfDart]
    rw [triangularTorusGraphDartDirection_symm]
    apply triangularKacWardTurnMatrix_eq_localRoots_of_rank_gt rho hrho
    rw [triangularTorusLocalPortOrder_rank,
      triangularTorusLocalPortOrder_rank] at hrank
    simp only [kwDartOfPort_portOfDart,
      triangularTorusGraphDartDirection_symm] at hrank
    exact hrank
  root_ne_zero p := by
    unfold triangularTorusLocalPortRoot
    exact zpow_ne_zero _ (triangularTorusTurnRoot_ne_zero rho hrho)
  root_sq_symm d := by
    unfold triangularTorusLocalPortRoot
    simp only [kwDartOfPort_portOfDart,
      triangularTorusGraphDartDirection_symm]
    have hrho0 := triangularTorusTurnRoot_ne_zero rho hrho
    have hrho8 := triangularTorusTurnRoot_pow_eight rho hrho
    generalize triangularTorusGraphDartDirection L d = a
    fin_cases a <;>
      simp [triangularTorusDirectionReverse,
        triangularTorusDirectionSignedAngle] <;>
      field_simp <;>
      simp [hrho, hrho8]


end StatMech.FrontierA
