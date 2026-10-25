/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForest
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

open StatMech.Ising

noncomputable section

theorem surfaceSpinLinearParity_local_add
    (a b x y x' y' : Fin 2) :
    a * (x + x') + b * (y + y') =
      (a * x + b * y) + (a * x' + b * y') := by
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    fin_cases x' <;> fin_cases y' <;> decide

theorem surfaceSpinLinearParity_add {g : Nat}
    (lambda : SurfaceSpinStructure g) (h k : SurfaceHomology g) :
    surfaceSpinLinearParity lambda (h + k) =
      surfaceSpinLinearParity lambda h + surfaceSpinLinearParity lambda k := by
  unfold surfaceSpinLinearParity
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact surfaceSpinLinearParity_local_add
    (lambda.1 i) (lambda.2 i) (h.1 i) (h.2 i) (k.1 i) (k.2 i)

end
end StatMech.FrontierA
