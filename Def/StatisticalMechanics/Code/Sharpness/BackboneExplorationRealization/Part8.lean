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
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part6
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace shb_BackboneExplorationDomain

variable (d : shb_BackboneExplorationDomain V)


noncomputable def LocalDomainResummation (β : ℝ) (J : Sym2 V → ℝ) : Prop := by
  classical
  exact ∀ (d k : shb_BackboneExplorationDomain V) (hdk : d ≤ k)
      (s : shb_AmbientSegment V) (hs : s ∈ d.active),
      let hd := d.active_supported s hs
      shb_P3DomainResummation d.graph k.graph hdk.1 β J (s.toPath d.graph hd)

end shb_BackboneExplorationDomain
end
end StatMech.Sharpness
