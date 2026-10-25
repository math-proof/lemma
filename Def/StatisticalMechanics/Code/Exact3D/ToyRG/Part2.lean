/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ToyRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Abbrev.StatisticalMechanics.Code.Exact3D.ToyRG


namespace StatMech

namespace Exact3D

noncomputable def toyRGMap (scale : BlockScale) (thermalEigenvalue : ℝ) :
    BlockSpinMap toyHamiltonianSpace where
  scale := scale
  map := fun x => thermalEigenvalue * x


noncomputable def toyFixedPointData (scale : BlockScale) {thermalEigenvalue : ℝ}
    (hthermal : 1 < thermalEigenvalue) :
    RGFixedPointData toyHamiltonianSpace (toyRGMap scale thermalEigenvalue) where
  fixedPoint := 0
  fixedPoint_eq := by simp [toyRGMap]
  thermalEigenvalue := thermalEigenvalue
  thermal_gt_one := hthermal


noncomputable def toyCertificate (scale : BlockScale) {thermalEigenvalue : ℝ}
    (hthermal : 1 < thermalEigenvalue) :
    RGCertificate (ToyCriticalModel scale thermalEigenvalue) where
  H := toyHamiltonianSpace
  R := toyRGMap scale thermalEigenvalue
  fixedPointData := toyFixedPointData scale hthermal


def toyCertificate_valid (scale : BlockScale) {thermalEigenvalue : ℝ}
    (hthermal : 1 < thermalEigenvalue) (correlationLength : ℝ → ℝ)
    (hbridge :
      HasCriticalNu (ToyCriticalModel scale thermalEigenvalue) correlationLength
        (predictedNu scale thermalEigenvalue)) :
    (toyCertificate scale hthermal).Valid correlationLength := by
  refine ⟨trivial, trivial, ?_, ?_, ?_, trivial, ?_⟩
  · exact (toyFixedPointData scale hthermal).fixedPoint_eq
  · exact (toyCertificate scale hthermal).linearizationEnclosure_of_thermal_gt_one
  · exact (toyCertificate scale hthermal).hyperbolicSplitting_of_thermal_gt_one
  · simpa [RGCertificate.RGToExponentBridge, RGCertificate.predictedExponent,
      toyCertificate] using hbridge


end Exact3D
end StatMech
