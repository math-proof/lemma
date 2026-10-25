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
import Instance.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part3
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

noncomputable def shb_AmbientSegment.toPath
    (H : SimpleGraph V) (s : shb_AmbientSegment V) (h : s.Supported H) :
    H.Path s.1 s.2.1 :=
  ⟨s.2.2.1.transfer H h, s.2.2.2.transfer h⟩

end
end StatMech.Sharpness
