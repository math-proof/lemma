/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Abbrev.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part3


namespace StatMech

namespace Exact3D

namespace TwoCoordinateRGData

noncomputable def rgMap (D : TwoCoordinateRGData) : BlockSpinMap D.hamiltonian where
  scale := D.scale
  map := fun x => (D.thermal * x.1, D.stable * x.2)


noncomputable def fixedPointData (D : TwoCoordinateRGData) :
    RGFixedPointData D.hamiltonian D.rgMap where
  fixedPoint := (0, 0)
  fixedPoint_eq := by
    simp [rgMap]
  thermalEigenvalue := D.thermal
  thermal_gt_one := D.thermal_gt_one


noncomputable def model (_D : TwoCoordinateRGData) : CriticalModel Unit where
  betaC := 0
  twoPoint := fun _ _ _ => 0


noncomputable def certificate (D : TwoCoordinateRGData) : RGCertificate D.model where
  H := D.hamiltonian
  R := D.rgMap
  fixedPointData := D.fixedPointData


noncomputable def nu (D : TwoCoordinateRGData) : ℝ :=
  D.certificate.predictedExponent


noncomputable def exactScaleObservable (D : TwoCoordinateRGData) (β : ℝ) : ℝ :=
  Real.exp (-D.nu * Real.log (-β))


noncomputable def iterate (D : TwoCoordinateRGData) :
    ℕ → (ℝ × ℝ) → (ℝ × ℝ)
  | 0, x => x
  | n + 1, x => D.rgMap.map (D.iterate n x)


end TwoCoordinateRGData
end Exact3D
end StatMech
