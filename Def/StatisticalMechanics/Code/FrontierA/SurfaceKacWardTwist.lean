/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForest
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

open StatMech.Ising

noncomputable section

def surfaceSpinLinearParity {g : Nat}
    (lambda : SurfaceSpinStructure g) (h : SurfaceHomology g) : Fin 2 :=
  ∑ i, (lambda.1 i * h.1 i + lambda.2 i * h.2 i)

end
end StatMech.FrontierA
