/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicScalingReduction
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation
open Filter Set Topology Metric


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


theorem normalizedInterpolant_medial (n : Nat) (e : A.M n) :
    A.normalizedInterpolant n (A.medialEmbedding n e) =
      @FKIsingDobrushinDomain.normalizedFermionicObservable
        (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e := by
  unfold normalizedInterpolant isingFermionicNormalizedInterpolant
  rw [A.rawInterpolant_medial n e]
  rfl


theorem compact_eventually_near_medial
    (K : Set Complex) (hKcompact : IsCompact K) (hKU : K ⊆ A.U) :
    ∀ᶠ n in atTop, ∀ z ∈ K,
      ∃ e : A.M n, dist z (A.medialEmbedding n e) ≤ A.mesh n := by
  filter_upwards [A.compact_eventually_mem K hKcompact hKU] with n hn
  intro z hz
  exact A.carrier_near_medial n z (hn hz)


end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
