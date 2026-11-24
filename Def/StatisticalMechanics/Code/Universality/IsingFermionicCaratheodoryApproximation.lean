module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicScalingReduction
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
public import Structure.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation
open Filter Set Topology Metric


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryApproximation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


noncomputable def normalizedInterpolant : Nat → Complex → Complex :=
  isingFermionicNormalizedInterpolant A.mesh A.rawInterpolant


end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
