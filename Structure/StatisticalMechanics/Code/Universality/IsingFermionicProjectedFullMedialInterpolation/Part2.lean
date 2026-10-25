/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicProjectedFullMedialInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialRegularity.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialInterpolation.Part7
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDiscreteInterpolation.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicProjectedFullMedialInterpolation.Part2
open Filter Metric Set Topology


noncomputable section

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC


namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


structure BoundaryRadialTensorTentGeometry where
  n : Nat → Nat
  m : Nat → Nat
  hn : ∀ k, 0 < n k
  hm : ∀ k, m k ≤ n k
  i : ∀ k, A.M k → Fin (m k)
  j : ∀ k, A.M k → Fin (m k)
  side : ∀ k, A.M k → FKIsingMedialSide
  embedding_eq : ∀ k e,
    A.medialEmbedding k e =
      isingRadialGridPosition (A.mesh k) (i k e).1 (j k e).1
  observable_eq : ∀ k e,
    @FKIsingDobrushinDomain.normalizedFermionicObservable
        (A.P k) (A.M k) (A.decEqM k) (A.dobrushin k) (A.mesh k) e =
      (fkIsingSquareBoundaryRestrictedDobrushinDomain (n k) (hn k)).normalizedFermionicObservable
        (A.mesh k)
          (.dart (fkIsingSquareRadialPatchEdge
            (n k) (m k) (hm k) (i k e) (j k e), side k e))


end FKIsingCaratheodoryApproximation
end StatMech.Universality
end
