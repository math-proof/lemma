/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePerimeterReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeThermodynamicReduction.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugePerimeterReduction.Part3
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

def gaugePerimeterPenalty (R : Real) : Real :=
  -Real.log (1 - R) / R

end
end StatMech.FrontierA
