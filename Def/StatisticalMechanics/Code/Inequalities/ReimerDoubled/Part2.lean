/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerStep.Part3
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


noncomputable def boxDoubled (𝒜 ℬ : Finset (Finset α)) : Finset (Finset (α ⊕ α)) :=
  ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).image (fun p => dbl p.1 p.2)


end StatMech
