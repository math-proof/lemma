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
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part15


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassFKPCLogAffineNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  pδ : ℝ
  pδ_pos : 0 < pδ
  logRemainder : ℝ → ℝ
  fkMass_pos :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
      0 < fkMass p
  logRemainder_negligible :
    Filter.Tendsto
      (fun p : ℝ => logRemainder p / Real.log (Ising3DFKPC - p))
      (nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC)) (nhds 0)
  log_fk_mass_scaling :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
      Real.log (fkMass p) =
        C.predictedExponent * Real.log (Ising3DFKPC - p) +
          logRemainder p

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassFKPCLogRatioLimitNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  pδ : ℝ
  pδ_pos : 0 < pδ
  fkMass_pos :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
      0 < fkMass p
  log_fk_mass_ratio_tendsto :
    Filter.Tendsto
      (fun p : ℝ =>
        Real.log (fkMass p) / Real.log (Ising3DFKPC - p))
      (nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC))
      (nhds C.predictedExponent)

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassFKPCLogRatioSandwichNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  pδ : ℝ
  pδ_pos : 0 < pδ
  fkMass_pos :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
      0 < fkMass p
  log_fk_mass_ratio_sandwich :
    ∀ ε, 0 < ε →
      ∀ᶠ p in nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC),
        C.predictedExponent - ε <
            Real.log (fkMass p) / Real.log (Ising3DFKPC - p) ∧
          Real.log (fkMass p) / Real.log (Ising3DFKPC - p) <
            C.predictedExponent + ε

end Exact3D
end StatMech
