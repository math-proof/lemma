/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonSupport
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

instance wilsonFreeEnergyPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

end
end StatMech.FrontierA
