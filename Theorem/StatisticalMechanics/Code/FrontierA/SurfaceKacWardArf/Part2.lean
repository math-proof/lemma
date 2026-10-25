/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf.Part2
open scoped BigOperators

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

theorem surfaceLocalArfQuadratic_sum (x y : Fin 2) :
    (∑ ab : Fin 2 × Fin 2,
      surfaceParitySign (surfaceLocalArfQuadraticExponent x y ab.1 ab.2)) = 2 := by
  fin_cases x <;> fin_cases y <;>
    simp [Fin.sum_univ_two, Fintype.sum_prod_type,
      surfaceLocalArfQuadraticExponent, surfaceParitySign, Fin.val_add] <;>
    norm_num

theorem surfaceArf_add_quadratic_eq_sum_local {g : Nat}
    (lambda : SurfaceSpinStructure g) (h : SurfaceHomology g) :
    surfaceArfParity lambda + surfaceQuadraticParity lambda h =
      ∑ i, surfaceLocalArfQuadraticExponent
        (h.1 i) (h.2 i) (lambda.1 i) (lambda.2 i) := by
  unfold surfaceArfParity surfaceQuadraticParity surfaceLocalArfQuadraticExponent
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  abel

end StatMech.FrontierA
