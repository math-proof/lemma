/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf.Part2
open scoped BigOperators

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable def surfaceSpinFunctionEquiv (g : Nat) :
    SurfaceSpinStructure g ≃ (Fin g → Fin 2 × Fin 2) :=
  (Equiv.arrowProdEquivProdArrow (Fin g)
    (fun _ : Fin g => Fin 2) (fun _ : Fin g => Fin 2)).symm

end StatMech.FrontierA
