/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Structure.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector.Part3
open Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

namespace shb_ExplorationRhoRealization

variable {D E : Type*} [Preorder D] [DecidableEq E]


theorem P2 (R : shb_ExplorationRhoRealization D E)
    (d : D) (p q : List E) :
    R.rho d (p ++ q) =
      R.rho d p * R.rho (R.kernel.exploration.residual d p) q := by
  rw [R.rho_eq_weight, R.kernel.weight_append,
    ← R.rho_eq_weight, ← R.rho_eq_weight]


theorem P3 (R : shb_ExplorationRhoRealization D E)
    {small large : D} (h : small ≤ large) (p : List E) :
    R.rho large p ≤ R.rho small p := by
  rw [R.rho_eq_weight, R.rho_eq_weight]
  exact R.kernel.weight_antitone h p


theorem rho_nonneg (R : shb_ExplorationRhoRealization D E)
    (d : D) (p : List E) : 0 ≤ R.rho d p := by
  rw [R.rho_eq_weight]
  exact R.kernel.weight_nonneg d p

end shb_ExplorationRhoRealization
end StatMech.Sharpness
