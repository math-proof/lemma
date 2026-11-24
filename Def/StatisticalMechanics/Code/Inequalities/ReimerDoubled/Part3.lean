module
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerStep.Part3
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part2
open Finset
open scoped FinsetFamily


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

variable {α : Type*} [DecidableEq α]


noncomputable def upComp (a : α ⊕ α) (𝒜 : Finset (Finset (α ⊕ α))) : Finset (Finset (α ⊕ α)) :=
  UV.compression {a} ∅ 𝒜


end StatMech
