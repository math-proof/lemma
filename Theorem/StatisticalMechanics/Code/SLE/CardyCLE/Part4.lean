/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CardyCLE.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.SLE.Defs.Part9
import Theorem.StatisticalMechanics.Code.SLE.Cardy.Part8
import Def.StatisticalMechanics.Code.SLE.CardyCLE.Part4
open scoped UpperHalfPlane NNReal
open Complex Filter Topology


namespace StatMech.SLE

@[simp] lemma mem_cleParameterSet {κ : ℝ} : κ ∈ cleParameterSet ↔ IsCLEParameter κ :=
  Iff.rfl


lemma cleParameterSet_subset_pos : cleParameterSet ⊆ {κ : ℝ | 0 < κ} :=
  fun _ hκ => IsCLEParameter.pos hκ


lemma kappaPercolation_mem_cleParameterSet : kappaPercolation ∈ cleParameterSet := by
  refine ⟨?_, ?_⟩ <;> norm_num [kappaPercolation]


lemma kappaFKIsing_mem_cleParameterSet : kappaFKIsing ∈ cleParameterSet := by
  refine ⟨?_, ?_⟩ <;> norm_num [kappaFKIsing]


lemma kappaIsing_mem_cleParameterSet : kappaIsing ∈ cleParameterSet := by
  refine ⟨?_, ?_⟩ <;> norm_num [kappaIsing]


end StatMech.SLE
