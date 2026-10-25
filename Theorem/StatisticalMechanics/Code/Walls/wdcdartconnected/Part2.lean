/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdcdartconnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wotsorbitsurj.Part2
import Def.StatisticalMechanics.Code.Walls.wdcdartconnected.Part2
open SimpleGraph Function


namespace StatMech

namespace Wots

open StatMech.Lattice


theorem wdc_layerGraph_adj (K : Set (Site 2)) (a b : {v : Site 2 // v ∈ wdc_boundaryLayer K}) :
    (wdc_layerGraph K).Adj a b ↔
      KingAdj (a : Site 2) (b : Site 2) ∧
      ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable
        ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩ := Iff.rfl


theorem wdc_wots_adj_of_kingAdj_heads (K : Set (Site 2))
    (d1 d2 : {e : Dart // IsBoundaryDart K e})
    (hk : KingAdj d1.1.head d2.1.head)
    (hr : ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable
      ⟨d1.1.head, d1.2.2⟩ ⟨d2.1.head, d2.2.2⟩) :
    (wots_dartGraph K).Adj d1 d2 := by
  refine ⟨?_, Or.inl hk, hr⟩
  intro h
  exact hk.1 (by rw [h])


theorem wdc_wots_adj_of_eq_heads (K : Set (Site 2))
    (d1 d2 : {e : Dart // IsBoundaryDart K e})
    (hne : d1 ≠ d2) (heq : d1.1.head = d2.1.head) :
    (wots_dartGraph K).Adj d1 d2 := by
  refine ⟨hne, Or.inr heq, ?_⟩
  have : (⟨d1.1.head, d1.2.2⟩ : (Kᶜ : Set (Site 2))) = ⟨d2.1.head, d2.2.2⟩ := Subtype.ext heq
  rw [this]


end Wots
end StatMech
