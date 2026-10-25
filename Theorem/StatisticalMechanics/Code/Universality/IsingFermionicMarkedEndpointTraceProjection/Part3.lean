/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicMarkedEndpointTraceProjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryProjectionSampling.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointInputAssembly
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPolynomialEndpointConvergence.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointTraceProjection.Part2


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFourthOrderLayerProjectionAndRange
    {N : Nat -> Nat} {hN : forall k, 0 < N k}
    {Phi : Complex -> Complex} {mesh : Nat -> Real} {radius : Nat -> Nat}
    (Hfourth : PhysicalEndpointFourthOrderBulkData N Phi mesh radius)
    (Hlayer : PhysicalEndpointLayerIncrementData N Phi mesh radius)
    (P : PhysicalEndpointOrdinaryBoundaryProjectionData N Phi mesh radius)
    (hvertexRadius : forall k, 0 < radius k)
    (hfaceRadius : forall k, 2 <= radius k)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (hvertexRange : forall k x,
      0 <= (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im /\
        (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) x)).im <= 1)
    (hfaceRange : forall k c,
      0 <= (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im /\
        (Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) c)).im <= 1)
    (hscaledFourth_tendsto : Tendsto
      (fun k => |mesh k| ^ 4 * (N k : Real) ^ 2) atTop (nhds 0))
    (htrace_tendsto : Tendsto
      (fun k => (P.lipschitzConstant k : Real) * mesh k)
      atTop (nhds 0))
    (hmesh_tendsto : Tendsto mesh atTop (nhds 0)) :
    PhysicalEndpointLocalizedMarkedClampedRobinInputs N hN Phi mesh radius
      (fun k => (P.lipschitzConstant k : Real) * mesh k)
      (fun k => (Hfourth.boundOne + Hfourth.boundTwo) * |mesh k| ^ 4 / 12)
      (fun k => (4 * Hlayer.constant) * mesh k +
        (3 * isingFermionicGhostCoefficient) *
          ((P.lipschitzConstant k : Real) * mesh k))
      (fun _ => 4 + 3 * isingFermionicGhostCoefficient) :=
  PhysicalEndpointLocalizedMarkedClampedRobinInputs.ofFourthOrderLayerTraceAndRange
      Hfourth Hlayer
      (P.toOrdinaryTraceData hmesh_nonneg htrace_tendsto)
      hvertexRadius hfaceRadius hmesh_nonneg hvertexRange hfaceRange
      hscaledFourth_tendsto hmesh_tendsto

end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
