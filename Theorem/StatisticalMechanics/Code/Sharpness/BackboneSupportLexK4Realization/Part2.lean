/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Realization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
import Instance.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

@[simp] theorem shbK4Graph_mem_edgeSet_iff
    (E : Finset shbK4Edge) (e : Sym2 (Fin 4)) :
    e ∈ (shbK4Graph E).edgeSet ↔ e ∈ E.image shbK4Edge.code := by
  rw [shbK4Graph, SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    rw [Finset.mem_image] at h
    obtain ⟨k, _, rfl⟩ := h
    cases k <;> decide

@[simp] theorem shbK4Graph_edgeFinset
    (E : Finset shbK4Edge) :
    (shbK4Graph E).edgeFinset = E.image shbK4Edge.code := by
  ext e
  simp [SimpleGraph.mem_edgeFinset]


end StatMech.Sharpness
