/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSubsystem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeGKS.Part2
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeSubsystem
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

@[simp] theorem embeddingSplitEquiv_inl {A B : Type*}
    (f : A ↪ B) (a : A) :
    embeddingSplitEquiv f (.inl a) = f a := by
  simp [embeddingSplitEquiv, Equiv.sumCompl]

@[simp] theorem embeddingSplitEquiv_symm_apply {A B : Type*}
    (f : A ↪ B) (a : A) :
    (embeddingSplitEquiv f).symm (f a) = .inl a := by
  apply (embeddingSplitEquiv f).injective
  simp


end
end StatMech.FrontierA
