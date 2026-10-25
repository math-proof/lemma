/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdcdartconnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wotsorbitsurj.Part2
import Def.StatisticalMechanics.Code.Walls.wdcdartconnected.Part4
open SimpleGraph Function


namespace StatMech

namespace Wots

open StatMech.Lattice


theorem wdc_dartConnected_of_layerConnected (K : Set (Site 2))
    (h : wdc_LayerConnected K) : wots_DartConnected K := by
  intro d1 d2 hreach
  set a : {x : Site 2 // x ∈ wdc_boundaryLayer K} := ⟨d1.1.head, wdc_head_mem_layer K d1⟩ with ha
  set b : {x : Site 2 // x ∈ wdc_boundaryLayer K} := ⟨d2.1.head, wdc_head_mem_layer K d2⟩ with hb
  
  have g1 : (wots_dartGraph K).Reachable d1 (wdc_pick K a) := by
    by_cases hd : d1 = wdc_pick K a
    · rw [hd]
    · exact (wdc_wots_adj_of_eq_heads K d1 (wdc_pick K a) hd (by rw [wdc_pick_head])).reachable
  
  have g2 : (wots_dartGraph K).Reachable (wdc_pick K b) d2 := by
    by_cases hd : wdc_pick K b = d2
    · rw [hd]
    · exact (wdc_wots_adj_of_eq_heads K (wdc_pick K b) d2 hd (by rw [wdc_pick_head])).reachable
  
  have hlayer : (wdc_layerGraph K).Reachable a b := h a b hreach
  have hmid : (wots_dartGraph K).Reachable (wdc_pick K a) (wdc_pick K b) :=
    wdc_pick_reachable_of_layerReachable K hlayer
  exact (g1.trans hmid).trans g2


end Wots
end StatMech
