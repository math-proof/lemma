module
public import Theorem.StatisticalMechanics.Code.SLE.BrownianCompactCylinderIntersection.Part3
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
public import Def.StatisticalMechanics.Code.SLE.BrownianProjectiveExtension
open Filter MeasureTheory Set Topology
open scoped ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianProjectiveExtension.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.SLE

instance brownianProductLaw.isProbabilityMeasure :
    IsProbabilityMeasure brownianProductLaw where
  measure_univ := by
    rw [brownianProductLaw, AddContent.measure_eq]
    · exact brownianProjectiveContent_univ
    · exact generateFrom_measurableCylinders.symm
    · exact univ_mem_measurableCylinders fun _ : Real => Real


end StatMech.SLE
