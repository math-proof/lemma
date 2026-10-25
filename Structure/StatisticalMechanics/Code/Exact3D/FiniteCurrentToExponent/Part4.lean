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
import Abbrev.StatisticalMechanics.Code.Exact3D.FiniteCurrentToExponent


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


structure Ising3DTransitionAssemblyInputs where
  isingBox :
    ∀ β, 0 < β → ∀ n, 1 ≤ n →
      IsingFK.fvMagnetization 3 β n =
        IsingFK.esWiredOnePoint
          (FK.boxGraph 3 (n + 1))
          (FK.boxBoundary 3 (n + 1))
          (0 : Fin 2) (IsingFK.pOfBeta β)
          (IsingFK.boxOrigin 3 (n + 1))
  thetaPc :
    ∀ (hp : 0 < FK.fkPc 3 2) (hp1 : FK.fkPc 3 2 < 1),
      FK.fkTheta 3 hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0
  pc_lt_one : FK.fkPc 3 2 < 1

end Exact3D
end StatMech
