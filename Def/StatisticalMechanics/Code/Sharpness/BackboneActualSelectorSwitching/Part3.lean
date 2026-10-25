/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelectorAdmissible.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

noncomputable def shb_explorationCoordinateWeight
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) : Real :=
  weight d.graph beta J (ofEdgeFun d.graph m)


def shb_ActiveSegmentFiber
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (hs : s ∈ d.active) (m : d.graph.edgeFinset -> Nat) : Prop :=
  sources d.graph (ofEdgeFun d.graph m) = {s.1, s.2.1} /\
    shb_backboneSelectSupport d.graph (ofEdgeFun d.graph m) s.1 s.2.1 =
      some (s.toPath d.graph (d.active_supported s hs))

end
end StatMech.Sharpness
