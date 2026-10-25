/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Hierarchical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part15
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
import Abbrev.StatisticalMechanics.Code.Exact3D.Hierarchical


namespace StatMech

namespace Exact3D

noncomputable def hierarchicalRGMap : BlockSpinMap hierarchicalHamiltonianSpace where
  scale := hierarchicalScale
  map := fun x => (hierarchicalThermalEigenvalue * x.1,
    hierarchicalStableEigenvalue * x.2)


noncomputable def hierarchicalFixedPointData :
    RGFixedPointData hierarchicalHamiltonianSpace hierarchicalRGMap where
  fixedPoint := (0, 0)
  fixedPoint_eq := by simp [hierarchicalRGMap]
  thermalEigenvalue := hierarchicalThermalEigenvalue
  thermal_gt_one := hierarchical_thermal_gt_one


noncomputable def HierarchicalModel : CriticalModel Unit where
  betaC := 0
  twoPoint := fun _ _ _ => 0


noncomputable def hierarchicalCertificate : RGCertificate HierarchicalModel where
  H := hierarchicalHamiltonianSpace
  R := hierarchicalRGMap
  fixedPointData := hierarchicalFixedPointData


noncomputable def hierarchicalNu : ℝ :=
  hierarchicalCertificate.predictedExponent


noncomputable def hierarchicalCorrelationLength (β : ℝ) : ℝ :=
  Real.exp (-hierarchicalNu * Real.log (-β))


noncomputable def hierarchicalLinearization : Fin 2 → Fin 2 → ℝ
  | ⟨0, _⟩, ⟨0, _⟩ => hierarchicalThermalEigenvalue
  | ⟨1, _⟩, ⟨1, _⟩ => hierarchicalStableEigenvalue
  | _, _ => 0


def hierarchicalLinearizationIntervals : RatInterval.IntervalMatrix 2 2
  | ⟨0, _⟩, ⟨0, _⟩ => RatInterval.point 3
  | ⟨1, _⟩, ⟨1, _⟩ => RatInterval.point (1 / 2)
  | _, _ => RatInterval.point 0


noncomputable def hierarchicalStableLinearization : Fin 1 → Fin 1 → ℝ :=
  fun _ _ => hierarchicalStableEigenvalue


def hierarchicalStableLinearizationIntervals : RatInterval.IntervalMatrix 1 1 :=
  fun _ _ => RatInterval.point (1 / 2)


end Exact3D
end StatMech
