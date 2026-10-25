/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSignedPhysical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhysical.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part6
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSignedPhysical.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager


theorem two_mul_triangularTorusWeightedSpinCharacterSum_eq_walsh
    (L : Nat) [Fact (2 < L)]
    (weight : Sym2 (ZMod L × ZMod L) → Real) (a b : Fin 2) :
    (2 : Complex) * triangularTorusWeightedSpinCharacterSum L
        (fun edge => (weight edge : Complex)) a b =
      ∑ chi : Fin 2 × Fin 2,
        (triangularTorusQuadraticWalshSign a b chi : Complex) *
          triangularTorusWeightedLinearCharacterSum L weight chi := by
  classical
  unfold triangularTorusWeightedSpinCharacterSum
    triangularTorusWeightedLinearCharacterSum
  push_cast
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro F hF
  have hwalsh := congrArg (fun x : Real => (x : Complex))
    (two_mul_triangularTorus_spinCharacter_eq_walsh a b
      (triangularTorusEvenHomology L F))
  push_cast at hwalsh
  calc
    (2 : Complex) * ((ons_spinCharacter a b
          (triangularTorusEvenHomology L F) : Complex) *
        ∏ edge ∈ F, (weight edge : Complex)) =
      ((2 : Complex) * (ons_spinCharacter a b
        (triangularTorusEvenHomology L F) : Complex)) *
        ∏ edge ∈ F, (weight edge : Complex) := by ring
    _ = (∑ chi : Fin 2 × Fin 2,
          (triangularTorusQuadraticWalshSign a b chi : Complex) *
            (triangularTorusLinearCharacter chi
              (triangularTorusEvenHomology L F) : Complex)) *
        ∏ edge ∈ F, (weight edge : Complex) := by rw [hwalsh]
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro chi hchi
      ring


end StatMech.FrontierA
