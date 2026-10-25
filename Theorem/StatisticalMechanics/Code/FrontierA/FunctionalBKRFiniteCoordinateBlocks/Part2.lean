/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralFinite
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRFiniteCoordinateBlocks.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E D : Type*} [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D]
  {S : E → Type*} [∀ e, Fintype (S e)]


@[simp] theorem mem_piAgreementFiber {K : Set E} {x y : ∀ e, S e} :
    y ∈ piAgreementFiber K x ↔ piAgreeOn K x y := by
  classical
  simp [piAgreementFiber]

theorem piAgreementFiber_nonempty (K : Set E) (x : ∀ e, S e) :
    (piAgreementFiber K x).Nonempty := by
  classical
  exact ⟨x, mem_piAgreementFiber.mpr (piAgreeOn_refl K x)⟩


end StatMech.FrontierA
