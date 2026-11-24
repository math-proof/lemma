module
public import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
public import Theorem.StatisticalMechanics.Code.Ising.MonomialDisorder
public import Abbrev.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushin.Part2
open scoped BigOperators
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Ising

noncomputable section

instance rectangularPrismInteractionDecidableEq (m n h : Nat) :
    DecidableEq (RectangularPrismInteraction m n h) := Classical.decEq _


end
end StatMech.Ising
