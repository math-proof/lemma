/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerStep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Mathlib.Data.Finset.Prod
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


noncomputable def boxFamily (𝒜 ℬ : Finset (Finset α)) : Finset (Finset α) :=
  ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).image (fun p => p.1 ∪ p.2)


end StatMech
