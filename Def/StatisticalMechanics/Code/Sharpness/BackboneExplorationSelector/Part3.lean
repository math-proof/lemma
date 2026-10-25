/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Structure.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector.Part2
open Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

namespace shb_ExplorationKernel

variable {D E : Type*} [Preorder D] [DecidableEq E]


def weight (K : shb_ExplorationKernel D E) : D → List E → ℝ
  | _, [] => 1
  | d, e :: es => K.amplitude d e * K.weight (K.exploration.advance d e) es

end shb_ExplorationKernel
end StatMech.Sharpness
