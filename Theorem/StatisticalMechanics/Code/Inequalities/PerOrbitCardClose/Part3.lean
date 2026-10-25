/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part3
import Def.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part3
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem poc_perOrbitCard_iff_slabCard (A B : Set (ConfigSpace α)) :
    PerOrbitCard A B ↔ poc_SlabCard A B := by
  unfold PerOrbitCard poc_SlabCard
  constructor
  · intro h k; rw [← poc_card_boxOrbit, ← poc_card_imgOrbit]; exact h k
  · intro h k; rw [poc_card_boxOrbit, poc_card_imgOrbit]; exact h k


end StatMech
