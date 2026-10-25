/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForest
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part2
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

open StatMech.Ising

noncomputable section

theorem surfaceQuadraticParity_eq_base_add_linear {g : Nat}
    (lambda : SurfaceSpinStructure g) (h : SurfaceHomology g) :
    surfaceQuadraticParity lambda h =
      surfaceBaseQuadraticParity h + surfaceSpinLinearParity lambda h := by
  unfold surfaceQuadraticParity surfaceBaseQuadraticParity surfaceSpinLinearParity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  abel

@[simp] theorem surfaceQuadraticParity_zero {g : Nat} (h : SurfaceHomology g) :
    surfaceQuadraticParity (0 : SurfaceSpinStructure g) h =
      surfaceBaseQuadraticParity h := by
  rw [surfaceQuadraticParity_eq_base_add_linear]
  simp [surfaceSpinLinearParity]

end
end StatMech.FrontierA
