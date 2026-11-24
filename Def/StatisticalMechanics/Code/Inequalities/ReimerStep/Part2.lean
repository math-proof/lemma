module
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
public import Mathlib.Data.Finset.Prod
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerStep
open Finset
open scoped FinsetFamily


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

variable {α : Type*} [DecidableEq α]


def IsDownAtCoord (i : α) (𝒜 : Finset (Finset α)) : Prop := ∀ s ∈ 𝒜, s.erase i ∈ 𝒜


end StatMech
