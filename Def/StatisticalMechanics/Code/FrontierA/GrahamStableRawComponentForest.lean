/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Structure.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest
open Finset


namespace StatMech.GrahamGHS.FourColor

universe u v uI uW

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def FiniteRankTerminalSystem.terminalClosure
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (system : FiniteRankTerminalSystem A B) (a : A) : Finset B :=
  system.terminals a ∪ (system.children a).attach.biUnion
    (fun child => system.terminalClosure child.1)
termination_by system.rank a
decreasing_by exact system.children_rank_lt a child.1 child.2


def FiniteRankTerminalSystem.ReachesTerminal
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (system : FiniteRankTerminalSystem A B) (a : A) (terminal : B) : Prop :=
  terminal ∈ system.terminalClosure a

end StatMech.GrahamGHS.FourColor
