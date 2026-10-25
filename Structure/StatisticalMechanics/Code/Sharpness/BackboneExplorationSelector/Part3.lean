/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector.Part3
open Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

structure shb_ExplorationRhoRealization
    (D E : Type*) [Preorder D] [DecidableEq E] where
  kernel : shb_ExplorationKernel D E
  rho : D → List E → ℝ
  rho_eq_weight : ∀ d p, rho d p = kernel.weight d p

end StatMech.Sharpness
