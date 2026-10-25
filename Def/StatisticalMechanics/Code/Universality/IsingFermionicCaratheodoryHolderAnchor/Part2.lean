/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryHolderAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryHolderAnchor.Part2
open Filter Set Topology Metric


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


def HasEventualCompactAverageEnergy
    (support : ∀ n, Finset (A.M n)) : Prop :=
  A.HasEventualCompactAverageNormSq support ∧
    A.HasEventualCompactWindowDiameter support

end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
