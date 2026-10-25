/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyClose.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve.Part2
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve2
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


section Weighted

variable [Fintype α]


noncomputable def pairKernel' (w : α → Bool → ℝ) (i : α) (S T : Finset α) : ℝ :=
  if Disjoint S T then fwt' w i S * fwt' w i T else 0


end Weighted
end StatMech
