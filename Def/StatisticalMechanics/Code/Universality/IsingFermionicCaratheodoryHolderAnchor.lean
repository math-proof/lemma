/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryHolderAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryHolderAnchor
open Filter Set Topology Metric


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


def HasEventualCompactAverageNormSq
    (support : ∀ n, Finset (A.M n)) : Prop :=
  ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
    ∃ E : Real, 0 ≤ E ∧ ∀ᶠ n in atTop,
      (support n).Nonempty ∧
      (∑ a ∈ support n,
          Complex.normSq
            (@FKIsingDobrushinDomain.normalizedFermionicObservable
              (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) a)) ≤
        ((support n).card : Real) * E


def HasEventualCompactWindowDiameter
    (support : ∀ n, Finset (A.M n)) : Prop :=
  ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
    ∃ D : Real, 0 ≤ D ∧ ∀ᶠ n in atTop,
      ∀ a ∈ support n, ∀ e : A.M n,
        (∃ z ∈ K, dist z (A.medialEmbedding n e) ≤ A.mesh n) →
        dist (A.medialEmbedding n e) (A.medialEmbedding n a) ≤ D


end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
