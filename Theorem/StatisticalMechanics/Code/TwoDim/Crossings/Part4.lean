/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.TwoDim.Crossings.Part4
open Set


namespace StatMech

namespace TwoDim

open StatMech.Lattice

variable {a b : ℤ}


@[simp]
theorem mem_verticalCrossingEvent {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ verticalCrossingEvent a b ↔ VerticalCrossing ω a b := Iff.rfl


theorem HorizontalCrossing.connected {ω : ConfigSpace (Sym2 (Site 2))}
    (h : HorizontalCrossing ω a b) :
    ∃ (x y : Site 2), x ∈ leftSide a b ∧ y ∈ rightSide a b ∧ Connected 2 ω x y := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, x.2, y.2, hxy.connected⟩


theorem VerticalCrossing.connected {ω : ConfigSpace (Sym2 (Site 2))}
    (h : VerticalCrossing ω a b) :
    ∃ (x y : Site 2), x ∈ bottomSide a b ∧ y ∈ topSide a b ∧ Connected 2 ω x y := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, x.2, y.2, hxy.connected⟩


theorem openSubgraph_mono {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω') :
    openSubgraph 2 ω ≤ openSubgraph 2 ω' := by
  intro x y hxy
  refine ⟨hxy.1, ?_⟩
  have hle := h s(x, y)
  rw [hxy.2] at hle
  exact top_le_iff.mp hle


theorem connectedWithin_mono {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    {S : Set (Site 2)} {x y : S} (hxy : ConnectedWithin 2 ω S x y) :
    ConnectedWithin 2 ω' S x y := by
  refine hxy.mono ?_
  intro u v huv
  exact openSubgraph_mono h huv


theorem horizontalCrossingEvent_increasing {ω ω' : ConfigSpace (Sym2 (Site 2))}
    (h : ω ≤ ω') (hω : ω ∈ horizontalCrossingEvent a b) :
    ω' ∈ horizontalCrossingEvent a b := by
  obtain ⟨x, y, hxy⟩ := hω
  exact ⟨x, y, connectedWithin_mono h hxy⟩


theorem verticalCrossingEvent_increasing {ω ω' : ConfigSpace (Sym2 (Site 2))}
    (h : ω ≤ ω') (hω : ω ∈ verticalCrossingEvent a b) :
    ω' ∈ verticalCrossingEvent a b := by
  obtain ⟨x, y, hxy⟩ := hω
  exact ⟨x, y, connectedWithin_mono h hxy⟩

end TwoDim
end StatMech
