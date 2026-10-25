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
import Theorem.StatisticalMechanics.Code.SLE.BrownianProjectiveExtension
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.SLE

noncomputable def brownianProductLaw : Measure (Real -> Real) :=
  brownianProjectiveContent.measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge
    brownianProjectiveContent_isSigmaSubadditive

end StatMech.SLE
