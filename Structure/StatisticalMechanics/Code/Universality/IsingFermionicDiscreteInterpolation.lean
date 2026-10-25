/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiscreteInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Mathlib.Topology.UniformSpace.Ascoli
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiscreteInterpolation
open Filter Metric Set Topology
open scoped UniformConvergence


noncomputable section

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


structure StableDiscreteInterpolation where
  interpolant : Nat → Complex → Complex
  continuousOn : ∀ n, ContinuousOn (interpolant n) A.U
  medial : ∀ n e, interpolant n (A.medialEmbedding n e) =
    @FKIsingDobrushinDomain.normalizedFermionicObservable
      (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e
  compactEquicontinuous : ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
    EquicontinuousOn interpolant K

end FKIsingCaratheodoryApproximation
end StatMech.Universality
end
