/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterion.Part4
import Def.StatisticalMechanics.Code.Sharpness.BkCriterionFull
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph

variable {V : Type*}


@[simp] lemma shk_mem_boundaryPairs [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) [DecidableRel G.Adj] {q : V × V} :
    q ∈ shk_boundaryPairs G S ↔ q.1 ∈ S ∧ q.2 ∉ S ∧ G.Adj q.1 q.2 := by
  simp [shk_boundaryPairs]


theorem shk_firstExit_inclusion [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Set V) (S : Finset V) (B : Set V) (u : V)
    (huS : u ∈ S) (hBS : ∀ z ∈ B, z ∉ S) :
    connEvent G A u B ⊆
      ⋃ q ∈ shk_boundaryPairs G S, disjointOccurrence (connEvent G (S : Set V) u {q.1})
        (disjointOccurrence (edgeOpenEvent q.1 q.2) (connEvent G A q.2 B)) := by
  intro ω hω
  simp only [connEvent, Set.mem_setOf_eq] at hω
  obtain ⟨b, hbA, hbB, p, hpsupp⟩ := shk_walk_of_connToSet G ω A u B hω
  have hbypass_supp : ∀ z ∈ p.bypass.support, z ∈ A := fun z hz =>
    hpsupp z (p.support_bypass_subset hz)
  have hbS : b ∉ (S : Set V) := hBS b hbB
  obtain ⟨x, y, hxS, hynS, hGadj, htriple⟩ :=
    shk_firstExit_triple G ω A (S : Set V) B u b huS hbB hbS p.bypass p.bypass_isPath hbypass_supp
  rw [Set.mem_iUnion₂]
  exact ⟨(x, y), by rw [shk_mem_boundaryPairs]; exact ⟨hxS, hynS, hGadj⟩, htriple⟩

end Sharpness
end StatMech
