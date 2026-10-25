/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyClose.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]

section Weighted

variable [Fintype α]


noncomputable def wboxValue (w : α → Bool → ℝ) (𝒰 : Finset (Finset (α ⊕ α))) : ℝ :=
  (∏ x, w x true) ^ 2 * (𝒰.card : ℝ)


end Weighted
end StatMech
