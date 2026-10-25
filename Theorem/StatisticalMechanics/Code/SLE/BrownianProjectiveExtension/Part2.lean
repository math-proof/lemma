/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProjectiveExtension.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianCompactCylinderIntersection.Part3
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Instance.StatisticalMechanics.Code.SLE.BrownianProjectiveExtension
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.SLE

theorem brownianProductLaw_isProjectiveLimit :
    IsProjectiveLimit brownianProductLaw brownianFiniteDimensionalPiLaw := by
  intro I
  ext S hS
  rw [Measure.map_apply (Finset.measurable_restrict I) hS]
  change brownianProductLaw (cylinder I S) =
    brownianFiniteDimensionalPiLaw I S
  rw [brownianProductLaw, AddContent.measure_eq,
    brownianProjectiveContent_cylinder I S hS]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ hS

end StatMech.SLE
