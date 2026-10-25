/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushinSpinFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushin
import Def.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip
open scoped BigOperators
open Finset


namespace StatMech.Ising

noncomputable section

theorem rectangularPrismSpin_upperHalfFlip {m n h : Nat}
    (sigma : RectangularPrismConfig m n h)
    (x : Fin m) (y : Fin n) (z : Fin (2 * h + 1)) :
    rectangularPrismSpin (rectangularPrismUpperHalfFlip sigma) x y z =
      if h < z.val then -rectangularPrismSpin sigma x y z
      else rectangularPrismSpin sigma x y z := by
  by_cases hz : h < z.val <;>
    by_cases hs : sigma ⟨x, y, z⟩ <;>
      simp [rectangularPrismSpin, rectangularPrismUpperHalfFlip, spin, hz, hs]


end
end StatMech.Ising
