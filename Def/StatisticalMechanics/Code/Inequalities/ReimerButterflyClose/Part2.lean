module
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerClose2.Part4
public import Mathlib.Combinatorics.SetFamily.Compression.Down
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyClose.Part2
open Finset
open scoped FinsetFamily


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

variable {α : Type*} [DecidableEq α]


section Weighted

variable [Fintype α]


noncomputable def fwt (w : α → Bool → ℝ) (S : Finset α) : ℝ :=
  ∏ x, w x (decide (x ∈ S))


noncomputable def fwt' (w : α → Bool → ℝ) (i : α) (S : Finset α) : ℝ :=
  ∏ x ∈ univ.erase i, w x (decide (x ∈ S))


end Weighted
end StatMech
