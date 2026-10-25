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
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part10
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

noncomputable def shb_randomCurrentExplorationRealization
    (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (hdom : shb_BackboneExplorationDomain.LocalDomainResummation β J)
    (fiberMass : shb_ExplorationFiberMass V)
    (hcut : shb_LocalSelectorFiberCutResummation β J fiberMass) :
    shb_ExplorationRhoRealization (shb_ExplorationDomain V)
      (shb_ExplorationSegment V) where
  kernel := shb_BackboneExplorationDomain.kernel β J hβ hJ hdom
  rho := shb_normalizedExplorationRho β J fiberMass
  rho_eq_weight := shb_randomCurrent_rho_eq_weight β J hβ hJ hdom fiberMass hcut

end
end StatMech.Sharpness
