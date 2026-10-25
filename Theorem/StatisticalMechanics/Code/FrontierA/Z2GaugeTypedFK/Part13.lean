/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part15
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem typedESTwoPoint_eq_typedFKTwoPoint
    (ends : P -> V × V) (rho : P -> Real) (x y : V) :
    typedESTwoPoint ends rho x y = typedFKTwoPoint ends rho x y := by
  classical
  unfold typedESTwoPoint typedFKTwoPoint typedFKEventMass typedFKProb
  simp_rw [typedESWeight_spinProduct_sum_eq]
  rw [typedFKZ_eq_typedESZ_empty, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro omega _
  by_cases hxy : (typedOpenGraph ends omega).Reachable x y
  · simp [typedFKConnEvent, hxy]
  · simp [typedFKConnEvent, hxy]


end
end StatMech.FrontierA
