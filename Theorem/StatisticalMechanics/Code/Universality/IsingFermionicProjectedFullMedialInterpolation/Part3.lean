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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicProjectedFullMedialInterpolation
open Filter Metric Set Topology


noncomputable section

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC


namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


theorem BoundaryRadialTensorTentGeometry.interpolant_continuous
    (A : FKIsingCaratheodoryApproximation)
    (G : BoundaryRadialTensorTentGeometry A) (k : Nat) :
    Continuous (BoundaryRadialTensorTentGeometry.interpolant A G k) :=
  fkIsingSquareBoundaryRadialPatchInterpolant_continuous
    (G.n k) (G.m k) (G.hn k) (G.hm k) (A.mesh k)

theorem BoundaryRadialTensorTentGeometry.projectedMedial
    (A : FKIsingCaratheodoryApproximation)
    (G : BoundaryRadialTensorTentGeometry A) (k : Nat) (e : A.M k) :
    isingProj
        (BoundaryRadialTensorTentGeometry.tangent A G k e)
        (BoundaryRadialTensorTentGeometry.interpolant A G k
          (A.medialEmbedding k e)) =
      @FKIsingDobrushinDomain.normalizedFermionicObservable
        (A.P k) (A.M k) (A.decEqM k) (A.dobrushin k) (A.mesh k) e := by
  rw [G.embedding_eq k e]
  simp only [BoundaryRadialTensorTentGeometry.tangent,
    BoundaryRadialTensorTentGeometry.interpolant]
  rw [fkIsingSquareBoundaryRadialPatchInterpolant_projection
    (G.n k) (G.m k) (G.hn k) (G.hm k) (A.mesh k)
    (A.mesh_pos k) (G.i k e) (G.j k e) (G.side k e)]
  exact (G.observable_eq k e).symm


end FKIsingCaratheodoryApproximation
end StatMech.Universality
end
