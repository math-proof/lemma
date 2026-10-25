/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.IsingRGCoordinateBridge.Part2


namespace StatMech

namespace Exact3D

structure IsingRGCoordinateBridgeInputs
    (C : RGCertificate Ising3DModel) where
  scaffold : IsingRGCoordinateScaffold C
  lengthCovariance : scaffold.LengthCovariance
  coordinateCovariance : scaffold.CoordinateRGCovariance
  microscopicOrbitEntry : scaffold.MicroscopicOrbitEntry
  stableManifoldControlStatement : Prop
  stableManifoldControl : stableManifoldControlStatement
  realizesXAxisLength :
    ∀ β, β ∈ scaffold.leftCriticalInterval →
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (scaffold.correlationLength β)
  prefactor_pos :
    ∀ β, β ∈ scaffold.leftCriticalInterval →
      0 < scaffold.prefactor β
  prefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ =>
        Real.log (scaffold.prefactor β) / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  extractsLengthScaling :
    scaffold.LengthCovariance →
      scaffold.CoordinateRGCovariance →
      stableManifoldControlStatement →
      scaffold.MicroscopicOrbitEntry →
        ∀ β, β ∈ scaffold.leftCriticalInterval →
          scaffold.correlationLength β =
            scaffold.prefactor β *
              Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))

end Exact3D
end StatMech
