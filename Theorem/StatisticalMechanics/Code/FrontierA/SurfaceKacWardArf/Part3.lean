/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf.Part3
open scoped BigOperators

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

@[simp] theorem surfaceSpinFunctionEquiv_apply_fst (g : Nat)
    (lambda : SurfaceSpinStructure g) (i : Fin g) :
    (surfaceSpinFunctionEquiv g lambda i).1 = lambda.1 i := rfl

@[simp] theorem surfaceSpinFunctionEquiv_apply_snd (g : Nat)
    (lambda : SurfaceSpinStructure g) (i : Fin g) :
    (surfaceSpinFunctionEquiv g lambda i).2 = lambda.2 i := rfl

theorem surface_arf_character_orthogonality (g : Nat)
    (h : SurfaceHomology g) :
    (∑ lambda : SurfaceSpinStructure g,
      surfaceParitySign
        (surfaceArfParity lambda + surfaceQuadraticParity lambda h)) =
      (2 : Real) ^ g := by
  calc
    (∑ lambda : SurfaceSpinStructure g,
        surfaceParitySign
          (surfaceArfParity lambda + surfaceQuadraticParity lambda h)) =
        ∑ f : Fin g → Fin 2 × Fin 2,
          ∏ i, surfaceParitySign
            (surfaceLocalArfQuadraticExponent
              (h.1 i) (h.2 i) (f i).1 (f i).2) := by
      apply Fintype.sum_equiv (surfaceSpinFunctionEquiv g)
      intro lambda
      rw [surfaceArf_add_quadratic_eq_sum_local, surfaceParitySign_sum]
      rfl
    _ = ∏ i : Fin g, ∑ ab : Fin 2 × Fin 2,
          surfaceParitySign
            (surfaceLocalArfQuadraticExponent
              (h.1 i) (h.2 i) ab.1 ab.2) :=
      (Fintype.prod_sum (fun i (ab : Fin 2 × Fin 2) =>
        surfaceParitySign (surfaceLocalArfQuadraticExponent
          (h.1 i) (h.2 i) ab.1 ab.2))).symm
    _ = (2 : Real) ^ g := by
      simp_rw [surfaceLocalArfQuadratic_sum]
      simp


end StatMech.FrontierA
