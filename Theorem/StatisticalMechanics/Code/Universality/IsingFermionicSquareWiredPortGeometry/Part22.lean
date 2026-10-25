/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part23


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

@[simp] theorem fkIsingSquareWiredUnitDiagonalAxis_zero :
    fkIsingSquareWiredUnitDiagonalAxis 0 = 2 := rfl

@[simp] theorem fkIsingSquareWiredUnitDiagonalAxis_one :
    fkIsingSquareWiredUnitDiagonalAxis 1 = 1 := rfl

@[simp] theorem fkIsingSquareWiredUnitDiagonalAxis_two :
    fkIsingSquareWiredUnitDiagonalAxis 2 = 3 := rfl

@[simp] theorem fkIsingSquareWiredUnitDiagonalAxis_three :
    fkIsingSquareWiredUnitDiagonalAxis 3 = 0 := rfl

theorem fkIsingSquareWiredIntPoint_unitDiagonal_eq_rotatedAxis
    (a : Fin 4) :
    fkIsingSquareWiredIntPoint (fkIsingSquareWiredUnitDiagonalStep a) =
      (1 + Complex.I) *
        StatMech.FrontierA.kwRectilinearVector
          (fkIsingSquareWiredUnitDiagonalAxis a) := by
  fin_cases a <;> apply Complex.ext <;>
    norm_num [fkIsingSquareWiredIntPoint,
      fkIsingSquareWiredUnitDiagonalStep,
      fkIsingSquareWiredUnitDiagonalAxis,
      StatMech.FrontierA.kwRectilinearVector,
      StatMech.Onsager.BaseCase.stepOf]

theorem fkIsingSquareWired_kwVectorTurnPhase_common_mul
    (z x y : Complex) (hz : z ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    StatMech.FrontierA.kwVectorTurnPhase (z * x) (z * y) =
      StatMech.FrontierA.kwVectorTurnPhase x y := by
  have hang :
      ((Complex.arg (z * y) : Real.Angle) -
          (Complex.arg (z * x) : Real.Angle)) =
        (Complex.arg y : Real.Angle) - (Complex.arg x : Real.Angle) := by
    rw [Complex.arg_mul_coe_angle hz hx,
      Complex.arg_mul_coe_angle hz hy]
    abel
  unfold StatMech.FrontierA.kwVectorTurnPhase
    StatMech.FrontierA.kwAngleTurnPhase
  rw [hang]


theorem fkIsingSquareWiredUnitDiagonal_turnPhase
    (a b : Fin 4)
    (hnu : fkIsingSquareWiredUnitDiagonalAxis b ≠
      fkIsingSquareWiredUnitDiagonalAxis a + 2) :
    StatMech.FrontierA.kwVectorTurnPhase
        (fkIsingSquareWiredIntPoint (fkIsingSquareWiredUnitDiagonalStep a))
        (fkIsingSquareWiredIntPoint (fkIsingSquareWiredUnitDiagonalStep b)) =
      Complex.exp
        (((((fkIsingSquareSignedEighthTurn
          (fkIsingSquareWiredUnitDiagonalTangentCode a)
          (fkIsingSquareWiredUnitDiagonalTangentCode b) : Int) : Real) *
            (Real.pi / 8) : Real) : Complex) * Complex.I) := by
  have hfac : (1 + Complex.I : Complex) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  rw [fkIsingSquareWiredIntPoint_unitDiagonal_eq_rotatedAxis,
    fkIsingSquareWiredIntPoint_unitDiagonal_eq_rotatedAxis]
  rw [fkIsingSquareWired_kwVectorTurnPhase_common_mul _ _ _ hfac
    (StatMech.FrontierA.kwRectilinearVector_ne_zero _)
    (StatMech.FrontierA.kwRectilinearVector_ne_zero _)]
  rw [StatMech.FrontierA.kwVectorTurnPhase_rectilinear _ _ hnu]
  fin_cases a <;> fin_cases b <;>
    norm_num [fkIsingSquareWiredUnitDiagonalAxis] at hnu
  all_goals simp [Fin.add_def, Fin.ext_iff] at hnu ⊢
  all_goals simp [
      fkIsingSquareSignedEighthTurn,
      StatMech.Onsager.ons_turnW,
      StatMech.Onsager.ons_turnRoot,
      Complex.exp_neg, div_eq_mul_inv, Fin.add_def,
      Fin.ext_iff] at hnu ⊢
  all_goals congr 1 <;> ring


end
end StatMech.Universality
