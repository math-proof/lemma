/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdcdartconnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wotsorbitsurj.Part2
import Def.StatisticalMechanics.Code.Walls.wdcdartconnected
open SimpleGraph Function


namespace StatMech

namespace Wots

open StatMech.Lattice


theorem wdc_layer_not_mem {K : Set (Site 2)} {v : Site 2} (hv : v ∈ wdc_boundaryLayer K) :
    v ∉ K := hv.1


theorem wdc_head_mem_layer (K : Set (Site 2)) (d : {e : Dart // IsBoundaryDart K e}) :
    d.1.head ∈ wdc_boundaryLayer K :=
  ⟨d.2.2, d.1.tail, d.1.adj, d.2.1⟩


theorem wdc_layer_isHead (K : Set (Site 2)) {v : Site 2} (hv : v ∈ wdc_boundaryLayer K) :
    ∃ d : {e : Dart // IsBoundaryDart K e}, d.1.head = v := by
  obtain ⟨hvK, s, hadj, hsK⟩ := hv
  exact ⟨⟨⟨s, v, hadj⟩, hsK, hvK⟩, rfl⟩


end Wots
end StatMech
