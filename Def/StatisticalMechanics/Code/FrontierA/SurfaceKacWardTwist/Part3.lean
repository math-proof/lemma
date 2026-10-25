/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardArf.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForest
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part2
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

open StatMech.Ising

noncomputable section

def surfaceHomologyCharacter {g : Nat}
    (lambda : SurfaceSpinStructure g) (h : SurfaceHomology g) : Complex :=
  (surfaceParitySign (surfaceSpinLinearParity lambda h) : Complex)

end
end StatMech.FrontierA
