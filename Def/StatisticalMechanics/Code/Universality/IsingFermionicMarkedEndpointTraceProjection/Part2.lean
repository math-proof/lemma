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
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicMarkedEndpointTraceProjection.Part2


namespace StatMech.Universality

open Filter Metric Set

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

noncomputable def
    PhysicalEndpointOrdinaryBoundaryProjectionData.toOrdinaryTraceData
    {N : Nat -> Nat} {Phi : Complex -> Complex}
    {mesh : Nat -> Real} {radius : Nat -> Nat}
    (P : PhysicalEndpointOrdinaryBoundaryProjectionData N Phi mesh radius)
    (hmesh_nonneg : forall k, 0 <= mesh k)
    (htrace_tendsto : Tendsto
      (fun k => (P.lipschitzConstant k : Real) * mesh k)
      atTop (nhds 0)) :
    PhysicalEndpointOrdinaryTraceData N Phi mesh radius
      (fun k => (P.lipschitzConstant k : Real) * mesh k) where
  trace_nonneg k := mul_nonneg (P.lipschitzConstant k).2 (hmesh_nonneg k)
  vertexFixed k x hfixed hghost :=
    (P.vertexFixed k x hfixed hghost).error_le (P.imPhi_lipschitz k)
  faceFixed k c hfixed hghost :=
    (P.faceFixed k c hfixed hghost).error_le (P.imPhi_lipschitz k)
  vertexFree k x hfixed hghost hendpoint :=
    (P.vertexFree k x hfixed hghost hendpoint).error_le
      (P.imPhi_lipschitz k)
  faceFree k c hfixed hghost hendpoint :=
    (P.faceFree k c hfixed hghost hendpoint).error_le
      (P.imPhi_lipschitz k)
  trace_tendsto := htrace_tendsto


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
