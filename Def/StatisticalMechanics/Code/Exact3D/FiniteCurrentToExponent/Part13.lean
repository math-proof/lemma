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
import Structure.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part14


namespace StatMech

namespace Exact3D

namespace FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical
      D fkMass where
  lowerPrefactor := h.lowerPrefactor
  pWindow := h.pWindow
  lowerPrefactor_pos := h.lowerPrefactor_pos
  pWindow_pos := h.pWindow_pos
  p_mass_lower_on_Ioo := by
    intro ε hε p hp
    simpa [hpred] using h.p_mass_lower_on_Ioo ε hε p hp

end FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerNearCritical

namespace FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical
      D fkMass where
  upperPrefactor := h.upperPrefactor
  pWindow := h.pWindow
  upperPrefactor_pos := h.upperPrefactor_pos
  pWindow_pos := h.pWindow_pos
  p_mass_upper_on_Ioo := by
    intro ε hε p hp
    simpa [hpred] using h.p_mass_upper_on_Ioo ε hε p hp

end FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperNearCritical

namespace FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical
      D fkMass where
  p_mass_lower_exists := by
    intro ε hε
    rcases h.p_mass_lower_exists ε hε with ⟨w, hw1, hw2, hbound⟩
    exact ⟨w, hw1, hw2, by
      intro q hq
      simpa [hpred] using hbound q hq⟩

end FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooLowerExistsNearCritical

namespace FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical

variable {C : RGCertificate Ising3DModel}

set_option linter.style.longLine false in


def congr_predictedExponent
    {D : RGCertificate Ising3DModel}
    {fkMass : ℝ → ℝ}
    (hpred : D.predictedExponent = C.predictedExponent)
    (h :
      FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
        C fkMass) :
    FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
      D fkMass where
  p_mass_upper_exists := by
    intro ε hε
    rcases h.p_mass_upper_exists ε hε with ⟨w, hw1, hw2, hbound⟩
    exact ⟨w, hw1, hw2, by
      intro q hq
      simpa [hpred] using hbound q hq⟩

end FreePositiveSubcriticalMassFKPCConstantPrefactorWeakIooUpperExistsNearCritical
end Exact3D
end StatMech
