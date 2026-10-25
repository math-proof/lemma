/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRFinite


namespace StatMech.FrontierA

open ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


@[simp] theorem mem_agreementFiber {K : Set E} {omega eta : ConfigSpace E} :
    eta ∈ agreementFiber K omega ↔ agreeOn K omega eta := by
  classical
  simp [agreementFiber]


theorem agreementFiber_nonempty (K : Set E) (omega : ConfigSpace E) :
    (agreementFiber K omega).Nonempty := by
  classical
  exact ⟨omega, mem_agreementFiber.mpr (agreeOn_refl K omega)⟩


end StatMech.FrontierA
