/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector.Part2
open Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

structure shb_ExplorationKernel (D E : Type*) [Preorder D] [DecidableEq E] where
  exploration : shb_DynamicEdgeExploration D E
  amplitude : D → E → ℝ
  amplitude_nonneg : ∀ d e, 0 ≤ amplitude d e
  amplitude_antitone : ∀ {small large}, small ≤ large → ∀ e,
    amplitude large e ≤ amplitude small e
  advance_mono : ∀ {small large}, small ≤ large → ∀ e,
    exploration.advance small e ≤ exploration.advance large e

end StatMech.Sharpness
