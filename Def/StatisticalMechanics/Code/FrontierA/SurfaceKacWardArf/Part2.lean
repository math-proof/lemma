/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf
open scoped BigOperators

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

def surfaceLocalArfQuadraticExponent
    (x y a b : Fin 2) : Fin 2 :=
  a * b + x * y + a * x + b * y

end StatMech.FrontierA
