/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf
open scoped BigOperators

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

@[simp] theorem surfaceParitySign_zero : surfaceParitySign 0 = 1 := by
  norm_num [surfaceParitySign]

theorem surfaceParitySign_add (z w : Fin 2) :
    surfaceParitySign (z + w) = surfaceParitySign z * surfaceParitySign w := by
  fin_cases z <;> fin_cases w <;> norm_num [surfaceParitySign, Fin.val_add]

theorem surfaceParitySign_finset_sum {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → Fin 2) :
    surfaceParitySign (∑ i ∈ S, f i) =
      ∏ i ∈ S, surfaceParitySign (f i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        surfaceParitySign_add, ih]

theorem surfaceParitySign_sum {g : Nat} (f : Fin g → Fin 2) :
    surfaceParitySign (∑ i, f i) = ∏ i, surfaceParitySign (f i) := by
  exact surfaceParitySign_finset_sum Finset.univ f

theorem surfaceQuadraticParity_local_add
    (a b x y x' y' : Fin 2) :
    (x + x') * (y + y') + a * (x + x') + b * (y + y') =
      (x * y + a * x + b * y) + (x' * y' + a * x' + b * y') +
        (x * y' + y * x') := by
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    fin_cases x' <;> fin_cases y' <;> decide

theorem surfaceQuadraticParity_add {g : Nat}
    (lambda : SurfaceSpinStructure g) (h k : SurfaceHomology g) :
    surfaceQuadraticParity lambda (h + k) =
      surfaceQuadraticParity lambda h + surfaceQuadraticParity lambda k +
        surfaceIntersection h k := by
  unfold surfaceQuadraticParity surfaceIntersection
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact surfaceQuadraticParity_local_add
    (lambda.1 i) (lambda.2 i) (h.1 i) (h.2 i) (k.1 i) (k.2 i)

end StatMech.FrontierA
