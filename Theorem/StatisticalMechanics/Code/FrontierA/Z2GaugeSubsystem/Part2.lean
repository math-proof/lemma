/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSubsystem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeGKS.Part2
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeSubsystem.Part2
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

@[simp] theorem gaugeConfigSplitEquiv_apply_emb {A B : Type*}
    (f : A ↪ B) (sigma : A → Bool)
    (tau : {b : B // b ∉ Set.range f} → Bool) (a : A) :
    gaugeConfigSplitEquiv f (sigma, tau) (f a) = sigma a := by
  simp [gaugeConfigSplitEquiv]


end
end StatMech.FrontierA
