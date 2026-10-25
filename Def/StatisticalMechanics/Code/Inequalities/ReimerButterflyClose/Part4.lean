/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerClose2.Part4
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyClose.Part4
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


def ReimerButterflyMono (n : ℕ) : Prop := ReimerSliceStep n


end StatMech
