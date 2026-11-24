module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
public import Mathlib.Topology.UniformSpace.Ascoli
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicDiscreteInterpolation
open Filter Metric Set Topology
open scoped UniformConvergence


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiscreteInterpolation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


variable (I : A.StableDiscreteInterpolation)


theorem StableDiscreteInterpolation.locallyUniformlySequentiallyPrecompact
    (E : StatMech.FrontierA.CompactExhaustion A.U)
    (hbounded : I.HasCompactLocalBounds) :
    StatMech.FrontierA.IsLocallyUniformlySequentiallyPrecompact
      I.interpolant A.U :=
  StatMech.FrontierA.equicontinuousFamily_locallyUniformlySequentiallyPrecompact_of_exhaustion
    I.interpolant A.U A.isOpen I.compactEquicontinuous hbounded E


end FKIsingCaratheodoryApproximation
end StatMech.Universality
end
