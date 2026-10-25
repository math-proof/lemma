/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalDirichletLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareDirichletConvergence.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalEnergy
open Filter Set Topology


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareSampledImaginaryPart
    (embedding : ∀ n, (fkSquareBoxPlanar n).V → Complex)
    (Phi : Complex → Complex) :
    ∀ n, (fkSquareBoxPlanar n).V → Real :=
  fun n x ↦ (Phi (embedding n x)).im


end
end StatMech.Universality
