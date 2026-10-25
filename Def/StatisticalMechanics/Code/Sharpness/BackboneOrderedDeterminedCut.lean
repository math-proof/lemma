/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Structure.StatisticalMechanics.Code.Sharpness.BackboneOrderedDeterminedCut
open Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

namespace shb_OrderedLocalTests

variable {E B : Type*} [DecidableEq E]


def testedThrough (T : shb_OrderedLocalTests E B) (accepted : E) : List E :=
  T.order.takeWhile (fun e => e != accepted) ++ [accepted]


def determinedCut (T : shb_OrderedLocalTests E B) (accepted : E) : Set B :=
  {b | ∃ e ∈ T.testedThrough accepted, b ∈ T.exposure e}


end shb_OrderedLocalTests
end
end StatMech.Sharpness
