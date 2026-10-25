/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSubsystem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeGKS.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeSubsystem
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

def gaugeConfigSplitEquiv {A B : Type*} (f : A ↪ B) :
    (A → Bool) × ({b : B // b ∉ Set.range f} → Bool) ≃ (B → Bool) :=
  (Equiv.sumArrowEquivProdArrow A {b : B // b ∉ Set.range f} Bool).symm |>.trans
    (Equiv.arrowCongr (embeddingSplitEquiv f) (Equiv.refl Bool))

end
end StatMech.FrontierA
