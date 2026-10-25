/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationRealization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2CutResummation.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP3Domain
import Instance.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part2
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

def shb_AmbientSegment.edgeSet (s : shb_AmbientSegment V) : Set (Sym2 V) :=
  {e | e ∈ s.2.2.1.edges}


def shb_AmbientSegment.Supported (H : SimpleGraph V)
    (s : shb_AmbientSegment V) : Prop :=
  ∀ e ∈ s.2.2.1.edges, e ∈ H.edgeSet

end
end StatMech.Sharpness
