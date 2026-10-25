/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.LatticeRG.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.IsingRGCoordinateBridge.Part6


namespace StatMech

namespace Exact3D

structure IsingMassRGCoordinateBridgeInputs
    (C : RGCertificate Ising3DModel) where
  scaffold : IsingMassRGCoordinateScaffold C
  massCovariance : scaffold.MassCovariance
  coordinateCovariance : scaffold.CoordinateRGCovariance
  microscopicOrbitEntry : scaffold.MicroscopicOrbitEntry
  stableManifoldControlStatement : Prop
  stableManifoldControl : stableManifoldControlStatement
  mass_pos :
    ∀ β, β ∈ scaffold.leftCriticalInterval →
      0 < scaffold.mass β
  realizesInverseXAxisLength :
    ∀ β, β ∈ scaffold.leftCriticalInterval →
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay (scaffold.mass β)
  correlationLength_eq_inv_mass :
    ∀ β, β ∈ scaffold.leftCriticalInterval →
      scaffold.correlationLength β = (scaffold.mass β)⁻¹
  massPrefactor_pos :
    ∀ β, β ∈ scaffold.leftCriticalInterval →
      0 < scaffold.massPrefactor β
  massPrefactor_log_negligible :
    Filter.Tendsto
      (fun β : ℝ =>
        Real.log (scaffold.massPrefactor β) / Real.log (Ising.betaC 3 - β))
      (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0)
  extractsMassScaling :
    scaffold.MassCovariance →
      scaffold.CoordinateRGCovariance →
      stableManifoldControlStatement →
      scaffold.MicroscopicOrbitEntry →
        ∀ β, β ∈ scaffold.leftCriticalInterval →
          scaffold.mass β =
            scaffold.massPrefactor β *
              Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))

end Exact3D
end StatMech
