/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushinSpinFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushin
import Instance.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip
open scoped BigOperators
open Finset


namespace StatMech.Ising

noncomputable section

def rectangularPrismUpperHalfFlip {m n h : Nat}
    (sigma : RectangularPrismConfig m n h) :
    RectangularPrismConfig m n h :=
  fun v => if h < v.z.val then !sigma v else sigma v


def rectangularPrismUpperHalfFlipEquiv (m n h : Nat) :
    RectangularPrismConfig m n h ≃ RectangularPrismConfig m n h where
  toFun := rectangularPrismUpperHalfFlip
  invFun := rectangularPrismUpperHalfFlip
  left_inv sigma := by
    funext v
    by_cases hz : h < v.z.val <;>
      simp [rectangularPrismUpperHalfFlip, hz]
  right_inv sigma := by
    funext v
    by_cases hz : h < v.z.val <;>
      simp [rectangularPrismUpperHalfFlip, hz]

end
end StatMech.Ising
