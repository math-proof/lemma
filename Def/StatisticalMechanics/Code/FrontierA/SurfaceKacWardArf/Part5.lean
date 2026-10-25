/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf.Part4
open scoped BigOperators

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable def surfaceTwistedSectorSquare {g : Nat}
    (weight : SurfaceHomology g → Real) (lambda : SurfaceSpinStructure g) : Real :=
  surfaceTwistedSectorRoot weight lambda ^ 2

end StatMech.FrontierA
