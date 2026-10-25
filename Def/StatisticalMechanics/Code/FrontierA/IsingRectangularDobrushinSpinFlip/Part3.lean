/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushinSpinFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushin
import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushinSpinFlip.Part2
open scoped BigOperators
open Finset


namespace StatMech.Ising

noncomputable section

def rectangularPrismDobrushinPartition
    (J beta : Real) (m n h : Nat) : Real :=
  monomialInteractionPartition
    (rectangularPrismDobrushinCoupling J beta :
      RectangularPrismInteraction m n h -> Real)
    (rectangularPrismInteractionMonomial :
      RectangularPrismInteraction m n h ->
        RectangularPrismConfig m n h -> Real)


end
end StatMech.Ising
