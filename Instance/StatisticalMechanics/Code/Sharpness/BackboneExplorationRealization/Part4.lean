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
import Structure.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace shb_BackboneExplorationDomain

variable (d : shb_BackboneExplorationDomain V)


instance : LE (shb_BackboneExplorationDomain V) where
  le d k := d.graph ≤ k.graph ∧ d.active = k.active

instance : Preorder (shb_BackboneExplorationDomain V) where
  le_refl d := ⟨le_rfl, rfl⟩
  le_trans d k l hdk hkl := ⟨hdk.1.trans hkl.1, hdk.2.trans hkl.2⟩


end shb_BackboneExplorationDomain
end
end StatMech.Sharpness
