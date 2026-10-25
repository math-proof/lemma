/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDiscreteInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Mathlib.Topology.UniformSpace.Ascoli
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicDiscreteInterpolation
open Filter Metric Set Topology
open scoped UniformConvergence


noncomputable section

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


variable (I : A.StableDiscreteInterpolation)


theorem stableInterpolant_compact_eventually_near_literalObservable
    (K : Set Complex) (hK : IsCompact K) (hKU : K ⊆ A.U) :
    ∀ᶠ n in atTop, ∀ z ∈ K, ∃ e : A.M n,
      dist z (A.medialEmbedding n e) ≤ A.mesh n ∧
      I.interpolant n (A.medialEmbedding n e) =
        @FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e := by
  filter_upwards [A.compact_eventually_near_medial K hK hKU] with n hn
  intro z hz
  obtain ⟨e, he⟩ := hn z hz
  exact ⟨e, he, I.medial n e⟩


end FKIsingCaratheodoryApproximation
end StatMech.Universality
end
