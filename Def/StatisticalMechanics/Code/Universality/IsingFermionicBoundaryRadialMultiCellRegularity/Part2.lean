/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryRadialMultiCellRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Mathlib.Algebra.Order.Chebyshev
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialMultiCellRegularity.Part3


namespace StatMech.Universality

open Filter Metric Set

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


noncomputable def StableFullMedialInterpolation.ofTensorTentCompactHolder
    (tangent : ∀ n, A.M n → Complex)
    (F : Nat → Complex → Complex)
    (hcontinuous : ∀ n, Continuous (F n))
    (hprojected : ∀ n e,
      isingProj (tangent n e) (F n (A.medialEmbedding n e)) =
        @FKIsingDobrushinDomain.normalizedFermionicObservable
          (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e)
    (H : A.MeshUniformCompactHolder F) :
    A.StableFullMedialInterpolation tangent where
  interpolant := F
  continuousOn n := (hcontinuous n).continuousOn
  projectedMedial := hprojected
  compactEquicontinuous K hK hKU :=
    MeshUniformCompactHolder.equicontinuousOn A H K hK hKU


noncomputable def BoundaryRadialTensorTentGeometry.toStableFullMedialInterpolationCompact
    (G : BoundaryRadialTensorTentGeometry A)
    (H : A.MeshUniformCompactHolder
      (BoundaryRadialTensorTentGeometry.interpolant A G)) :
    A.StableFullMedialInterpolation
      (BoundaryRadialTensorTentGeometry.tangent A G) :=
  StableFullMedialInterpolation.ofTensorTentCompactHolder A
    (BoundaryRadialTensorTentGeometry.tangent A G)
    (BoundaryRadialTensorTentGeometry.interpolant A G)
    (BoundaryRadialTensorTentGeometry.interpolant_continuous A G)
    (BoundaryRadialTensorTentGeometry.projectedMedial A G) H

end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
