/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part10
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusDissemination
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


@[simp] theorem isingTorusTranslateField_zero
    (u : IsingDyadicTorus d k → Real) :
    isingTorusTranslateField 0 u = u := by
  funext x
  simp [isingTorusTranslateField]

theorem isingTorusTranslateField_add
    (a : IsingDyadicTorus d k)
    (u v : IsingDyadicTorus d k → Real) :
    isingTorusTranslateField a (u + v) =
      isingTorusTranslateField a u + isingTorusTranslateField a v := by
  rfl

theorem isingTorusTranslateField_neg_add
    (a : IsingDyadicTorus d k)
    (u : IsingDyadicTorus d k → Real) :
    isingTorusTranslateField (-a) (isingTorusTranslateField a u) = u := by
  funext x
  simp [isingTorusTranslateField, add_assoc]

theorem isingTorusSpinField_translateConfig
    (a : IsingDyadicTorus d k)
    (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    isingTorusSpinField (isingTorusTranslateConfig a sigma) =
      isingTorusTranslateField a (isingTorusSpinField sigma) := by
  rfl

theorem isingTorusDirichlet_translateField
    (a : IsingDyadicTorus d k)
    (u : IsingDyadicTorus d k → Real) :
    isingTorusDirichlet (isingTorusTranslateField a u) =
      isingTorusDirichlet u := by
  unfold isingTorusDirichlet isingTorusDirichletBilinear
  rw [← (Equiv.addRight a).bijective.sum_comp
    (fun y : IsingDyadicTorus d k ↦
    ∑ i : Fin d, (u y - u (y + isingTorusStep i)) *
      (u y - u (y + isingTorusStep i)))]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro i _
  simp only [isingTorusTranslateField, Equiv.coe_addRight]
  congr 2 <;> congr 1
  all_goals abel

theorem isingTorusShiftedPartition_translateField
    (a : IsingDyadicTorus d k) (beta : Real)
    (h : IsingDyadicTorus d k → Real) :
    isingTorusShiftedPartition beta (isingTorusTranslateField a h) =
      isingTorusShiftedPartition beta h := by
  calc
    isingTorusShiftedPartition beta (isingTorusTranslateField a h) =
        ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
          Real.exp (-(beta / 2) * isingTorusDirichlet
            (isingTorusSpinField sigma + isingTorusTranslateField a h)) := rfl
    _ = ∑ sigma : ConfigSpace (IsingDyadicTorus d k),
          Real.exp (-(beta / 2) * isingTorusDirichlet
            (isingTorusSpinField (isingTorusTranslateConfig a sigma) +
              isingTorusTranslateField a h)) := by
        exact ((isingTorusTranslateConfigEquiv a).sum_comp (fun sigma =>
          Real.exp (-(beta / 2) * isingTorusDirichlet
            (isingTorusSpinField sigma +
              isingTorusTranslateField a h)))).symm
    _ = isingTorusShiftedPartition beta h := by
        unfold isingTorusShiftedPartition
        apply Finset.sum_congr rfl
        intro sigma _
        rw [isingTorusSpinField_translateConfig,
          ← isingTorusTranslateField_add,
          isingTorusDirichlet_translateField]


end StatMech.FrontierA
