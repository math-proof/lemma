/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSubsystem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeGKS.Part2
import Instance.StatisticalMechanics.Code.FrontierA.Z2GaugeSubsystem
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

def embeddingSplitEquiv {A B : Type*} (f : A ↪ B) :
    A ⊕ {b : B // b ∉ Set.range f} ≃ B :=
  (Equiv.sumCongr (Equiv.ofInjective f f.injective) (Equiv.refl _)).trans
    (Equiv.sumCompl fun b => b ∈ Set.range f)

end
end StatMech.FrontierA
