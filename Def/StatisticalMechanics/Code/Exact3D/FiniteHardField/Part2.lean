/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteHardField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteHardField
open Filter
open scoped BigOperators Topology


namespace StatMech

namespace Exact3D

noncomputable def hardFieldFactor {α : Type*} (good : α → Prop)
    [DecidablePred good] (H : ℝ) (a : α) : ℝ :=
  if good a then 1 else Real.exp (-H)


noncomputable def hardFieldNumerator {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base obs : α → ℝ)
    (H : ℝ) : ℝ :=
  ∑ a ∈ s, base a * hardFieldFactor good H a * obs a


noncomputable def hardFieldDenominator {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base : α → ℝ)
    (H : ℝ) : ℝ :=
  ∑ a ∈ s, base a * hardFieldFactor good H a


noncomputable def hardFieldLimitNumerator {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base obs : α → ℝ) : ℝ :=
  ∑ a ∈ s, if good a then base a * obs a else 0


noncomputable def hardFieldLimitDenominator {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base : α → ℝ) : ℝ :=
  ∑ a ∈ s, if good a then base a else 0


noncomputable def hardFieldRatio {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base obs : α → ℝ)
    (H : ℝ) : ℝ :=
  hardFieldNumerator s good base obs H /
    hardFieldDenominator s good base H


noncomputable def hardFieldLimitRatio {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base obs : α → ℝ) : ℝ :=
  hardFieldLimitNumerator s good base obs /
    hardFieldLimitDenominator s good base


end Exact3D
end StatMech
