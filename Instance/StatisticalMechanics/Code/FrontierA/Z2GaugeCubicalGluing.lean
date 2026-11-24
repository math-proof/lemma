module
public import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeSubsystem.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalWilson.Part3
public import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeRectangularThermodynamic
public import Theorem.StatisticalMechanics.Code.FrontierA.RectangularBlockTiling
open scoped BigOperators symmDiff
open Finset
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.flexible false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalGluing.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable section

instance z2GaugeCubicalGluingPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

end
end StatMech.FrontierA
