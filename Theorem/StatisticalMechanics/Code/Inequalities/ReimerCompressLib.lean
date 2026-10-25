/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerCompressLib.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve3.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Def.StatisticalMechanics.Code.Inequalities.ReimerCompressLib
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [DecidableEq α]


theorem isDownAt_of_isLowerSet {𝒜 : Finset (Finset α)}
    (h : IsLowerSet (𝒜 : Set (Finset α))) (i : α) : IsDownAt i 𝒜 :=
  fun _ hs => erase_mem_of_isLowerSet h hs i


theorem isLowerSet_iff_isDownAt_all (𝒜 : Finset (Finset α)) :
    IsLowerSet (𝒜 : Set (Finset α)) ↔ ∀ i, IsDownAt i 𝒜 := by
  constructor
  · exact fun h i => isDownAt_of_isLowerSet h i
  · intro h
    exact isLowerSet_of_erase_closed (fun s hs i => h i s hs)


end StatMech
