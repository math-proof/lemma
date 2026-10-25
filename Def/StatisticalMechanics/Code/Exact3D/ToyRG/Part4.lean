/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ToyRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Structure.StatisticalMechanics.Code.Exact3D.ToyRG


namespace StatMech

namespace Exact3D

noncomputable def toyHyperbolicFixedPointData (scale : BlockScale)
    {thermalEigenvalue stableEigenvalue : ℝ}
    (hthermal : 1 < thermalEigenvalue) :
    RGFixedPointData toyHyperbolicHamiltonianSpace
      (toyHyperbolicRGMap scale thermalEigenvalue stableEigenvalue) where
  fixedPoint := (0, 0)
  fixedPoint_eq := by simp [toyHyperbolicRGMap]
  thermalEigenvalue := thermalEigenvalue
  thermal_gt_one := hthermal


noncomputable def toyHyperbolicCertificate (scale : BlockScale)
    {thermalEigenvalue stableEigenvalue : ℝ}
    (hthermal : 1 < thermalEigenvalue) :
    RGCertificate (ToyCriticalModel scale thermalEigenvalue) where
  H := toyHyperbolicHamiltonianSpace
  R := toyHyperbolicRGMap scale thermalEigenvalue stableEigenvalue
  fixedPointData := toyHyperbolicFixedPointData scale hthermal


def toyHyperbolicCertificate_valid (scale : BlockScale)
    {thermalEigenvalue stableEigenvalue : ℝ}
    (hthermal : 1 < thermalEigenvalue)
    (_hstable : ToyStableCoordinate stableEigenvalue)
    (correlationLength : ℝ → ℝ)
    (hbridge :
      HasCriticalNu (ToyCriticalModel scale thermalEigenvalue) correlationLength
        (predictedNu scale thermalEigenvalue)) :
    (toyHyperbolicCertificate (stableEigenvalue := stableEigenvalue) scale hthermal).Valid
      correlationLength := by
  refine ⟨trivial, trivial, ?_, ?_, ?_, trivial, ?_⟩
  · exact (toyHyperbolicFixedPointData
      (stableEigenvalue := stableEigenvalue) scale hthermal).fixedPoint_eq
  · exact (toyHyperbolicCertificate
      (stableEigenvalue := stableEigenvalue) scale hthermal
      ).linearizationEnclosure_of_thermal_gt_one
  · exact (toyHyperbolicCertificate
      (stableEigenvalue := stableEigenvalue) scale hthermal
      ).hyperbolicSplitting_of_thermal_gt_one
  · simpa [RGCertificate.RGToExponentBridge, RGCertificate.predictedExponent,
      toyHyperbolicCertificate] using hbridge

end Exact3D
end StatMech
