/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushinSpinFlip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushin
open scoped BigOperators
open Finset


namespace StatMech.Ising

noncomputable section

instance rectangularPrismInteractionDecidableEq' (m n h : Nat) :
    DecidableEq (RectangularPrismInteraction m n h) := Classical.decEq _


end
end StatMech.Ising
