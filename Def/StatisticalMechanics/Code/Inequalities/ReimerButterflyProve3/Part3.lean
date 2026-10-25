/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve2.Part2
import Mathlib.Combinatorics.SetFamily.HarrisKleitman
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve3.Part3
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


noncomputable def totalSize (𝒜 : Finset (Finset α)) : ℕ := ∑ S ∈ 𝒜, S.card


end StatMech
