module
public import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelectorAdmissible.Part3
public import Structure.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching
open SimpleGraph Finset
open scoped BigOperators
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorSwitching.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

def shb_CurrentDynamicSelector.Fiber
    (S : shb_CurrentDynamicSelector (V := V))
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat) : Prop :=
  sources d.graph (ofEdgeFun d.graph m) = S.sourceClass d word /\
    S.select d m = word

end
end StatMech.Sharpness
