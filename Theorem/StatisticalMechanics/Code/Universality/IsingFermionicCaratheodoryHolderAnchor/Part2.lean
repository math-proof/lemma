/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryHolderAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryHolderAnchor
open Filter Set Topology Metric


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


theorem hasEventualCompactWindowDiameter_of_commonBall
    (support : ∀ n, Finset (A.M n))
    (hball : ∀ K : Set Complex, IsCompact K → K ⊆ A.U →
      ∃ center : Complex, ∃ R : Real, 0 ≤ R ∧ ∀ᶠ n in atTop,
        (∀ a ∈ support n, dist (A.medialEmbedding n a) center ≤ R) ∧
        ∀ e : A.M n,
          (∃ z ∈ K, dist z (A.medialEmbedding n e) ≤ A.mesh n) →
          dist (A.medialEmbedding n e) center ≤ R) :
    A.HasEventualCompactWindowDiameter support := by
  intro K hK hKU
  obtain ⟨center, R, hR, hevent⟩ := hball K hK hKU
  refine ⟨2 * R, mul_nonneg (by norm_num) hR, ?_⟩
  filter_upwards [hevent] with n hn
  intro a ha e he
  calc
    dist (A.medialEmbedding n e) (A.medialEmbedding n a) ≤
        dist (A.medialEmbedding n e) center +
          dist center (A.medialEmbedding n a) := dist_triangle _ _ _
    _ ≤ R + R := add_le_add (hn.2 e he) (by
      simpa [dist_comm] using hn.1 a ha)
    _ = 2 * R := by ring


end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
