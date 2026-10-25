/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteCurrentToExponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part136
import Theorem.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentTheorem
import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BcEqIsing
import Theorem.StatisticalMechanics.Code.Ising.TransitionAssembly
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part13


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
    (hmass : FreePositiveSubcriticalMassBridge)
    (fkMass : ℝ → ℝ)
    (hEq :
      ∀ᶠ β in nhdsWithin Ising3DFKBetaC (Set.Iio Ising3DFKBetaC),
        freeSelectedPositiveSubcriticalMass hmass β =
          fkMass (IsingFK.pOfBeta β)) :
    FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass := by
  classical
  let selectedWindow : ℝ :=
    Classical.choose
      (FKReparameterization.exists_Ioo_subset_of_eventually_left hEq)
  have hselectedWindow_spec :
      0 < selectedWindow ∧
        ∀ β, β ∈ Set.Ioo (Ising3DFKBetaC - selectedWindow) Ising3DFKBetaC →
          freeSelectedPositiveSubcriticalMass hmass β =
            fkMass (IsingFK.pOfBeta β) := by
    simpa [selectedWindow] using
      Classical.choose_spec
        (FKReparameterization.exists_Ioo_subset_of_eventually_left hEq)
  exact
    { fkMass := fkMass
      selectedWindow := fun _ => selectedWindow
      selectedWindow_pos := by
        intro _ _
        exact hselectedWindow_spec.1
      selected_mass_eq_fkMass := by
        intro _ _ β hβ
        exact hselectedWindow_spec.2 β hβ }

set_option linter.style.longLine false in


noncomputable def freePositiveSubcriticalMassFKPCSelectedAgreement_of_forallEq
    (hmass : FreePositiveSubcriticalMassBridge)
    (fkMass : ℝ → ℝ)
    (hEq :
      ∀ β,
        freeSelectedPositiveSubcriticalMass hmass β =
          fkMass (IsingFK.pOfBeta β)) :
    FreePositiveSubcriticalMassFKPCSelectedMassAgreementNearCritical hmass :=
  freePositiveSubcriticalMassFKPCSelectedAgreement_of_eventuallyEq
    hmass fkMass
    (Filter.Eventually.of_forall fun β => hEq β)

end Exact3D
end StatMech
