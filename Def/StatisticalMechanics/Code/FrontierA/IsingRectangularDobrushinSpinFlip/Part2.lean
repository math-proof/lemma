/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushinSpinFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushin
import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip
open scoped BigOperators
open Finset


namespace StatMech.Ising

noncomputable section

def rectangularPrismDobrushinCoupling
    (J beta : Real) {m n h : Nat} :
    RectangularPrismInteraction m n h -> Real
  | .inl _ => beta * J
  | .inr (.inl _) => beta * J
  | .inr (.inr (.inl _)) => beta * J
  | .inr (.inr (.inr v)) =>
      (if h < v.z.val then -1 else 1) *
        (beta * J * rectangularPrismBoundaryDegree v)

end
end StatMech.Ising
