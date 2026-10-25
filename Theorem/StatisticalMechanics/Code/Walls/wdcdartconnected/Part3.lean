/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdcdartconnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wotsorbitsurj.Part2
import Def.StatisticalMechanics.Code.Walls.wdcdartconnected.Part3
open SimpleGraph Function


namespace StatMech

namespace Wots

open StatMech.Lattice


@[simp] theorem wdc_pick_head (K : Set (Site 2)) (v : {x : Site 2 // x ∈ wdc_boundaryLayer K}) :
    (wdc_pick K v).1.head = v.1 :=
  (wdc_layer_isHead K v.2).choose_spec


theorem wdc_pick_reachable_of_layerReachable (K : Set (Site 2))
    {a b : {x : Site 2 // x ∈ wdc_boundaryLayer K}}
    (h : (wdc_layerGraph K).Reachable a b) :
    (wots_dartGraph K).Reachable (wdc_pick K a) (wdc_pick K b) := by
  obtain ⟨p⟩ := h
  suffices H : ∀ (u v : {x : Site 2 // x ∈ wdc_boundaryLayer K}), (wdc_layerGraph K).Walk u v →
      (wots_dartGraph K).Reachable (wdc_pick K u) (wdc_pick K v) from H a b p
  intro u v q
  induction q with
  | nil => exact Reachable.refl _
  | @cons u w v hadj q' ih =>
    refine Reachable.trans ?_ ih
    
    have hk : KingAdj (wdc_pick K u).1.head (wdc_pick K w).1.head := by
      rw [wdc_pick_head, wdc_pick_head]; exact hadj.1
    have hr : ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable
        ⟨(wdc_pick K u).1.head, (wdc_pick K u).2.2⟩ ⟨(wdc_pick K w).1.head, (wdc_pick K w).2.2⟩ := by
      have e1 : (⟨(wdc_pick K u).1.head, (wdc_pick K u).2.2⟩ : (Kᶜ : Set (Site 2)))
          = ⟨u.1, u.2.1⟩ := Subtype.ext (wdc_pick_head K u)
      have e2 : (⟨(wdc_pick K w).1.head, (wdc_pick K w).2.2⟩ : (Kᶜ : Set (Site 2)))
          = ⟨w.1, w.2.1⟩ := Subtype.ext (wdc_pick_head K w)
      rw [e1, e2]; exact hadj.2
    exact (wdc_wots_adj_of_kingAdj_heads K _ _ hk hr).reachable


end Wots
end StatMech
