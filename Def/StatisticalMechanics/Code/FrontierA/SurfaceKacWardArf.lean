/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardArf.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Abbrev.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf
open scoped BigOperators

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

def surfaceIntersection {g : Nat} (h k : SurfaceHomology g) : Fin 2 :=
  ∑ i, (h.1 i * k.2 i + h.2 i * k.1 i)

def surfaceQuadraticParity {g : Nat}
    (lambda : SurfaceSpinStructure g) (h : SurfaceHomology g) : Fin 2 :=
  ∑ i, (h.1 i * h.2 i + lambda.1 i * h.1 i + lambda.2 i * h.2 i)

def surfaceArfParity {g : Nat} (lambda : SurfaceSpinStructure g) : Fin 2 :=
  ∑ i, lambda.1 i * lambda.2 i

def surfaceParitySign (z : Fin 2) : Real := (-1 : Real) ^ z.val

end StatMech.FrontierA
