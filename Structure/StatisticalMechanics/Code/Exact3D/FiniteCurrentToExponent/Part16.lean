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
import Def.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent.Part14


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


structure FreePositiveSubcriticalMassFKPCAsymptoticPowerLawNearCritical
    (C : RGCertificate Ising3DModel)
    (fkMass : ℝ → ℝ) where
  pδ : ℝ
  pδ_pos : 0 < pδ
  amplitude : ℝ
  amplitude_pos : 0 < amplitude
  relativePrefactor : ℝ → ℝ
  relativePrefactor_tendsto_one :
    Filter.Tendsto relativePrefactor
      (nhdsWithin Ising3DFKPC (Set.Iio Ising3DFKPC)) (nhds 1)
  mass_scaling :
    ∀ p, p ∈ Set.Ioo (Ising3DFKPC - pδ) Ising3DFKPC →
      fkMass p =
        amplitude * relativePrefactor p *
          Real.exp (C.predictedExponent * Real.log (Ising3DFKPC - p))

end Exact3D
end StatMech
