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
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicProjectedFullMedialInterpolation.Part2
open Filter Metric Set Topology


noncomputable section

namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC


namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


noncomputable def BoundaryRadialTensorTentGeometry.interpolant
    (A : FKIsingCaratheodoryApproximation)
    (G : BoundaryRadialTensorTentGeometry A) :
    Nat → Complex → Complex := fun k =>
  fkIsingSquareBoundaryRadialPatchInterpolant
    (G.n k) (G.m k) (G.hn k) (G.hm k) (A.mesh k)


noncomputable def BoundaryRadialTensorTentGeometry.tangent
    (A : FKIsingCaratheodoryApproximation)
    (G : BoundaryRadialTensorTentGeometry A)
    (k : Nat) (e : A.M k) : Complex :=
  fkIsingSquareWiredDirectedTangent (G.n k) (G.hn k)
    (.dart (fkIsingSquareRadialPatchEdge
      (G.n k) (G.m k) (G.hm k) (G.i k e) (G.j k e), G.side k e))

end FKIsingCaratheodoryApproximation
end StatMech.Universality
end
