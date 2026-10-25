/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Def.StatisticalMechanics.Code.RSW.Defs.Part3
open Set


namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice

open StatMech.TwoDim


@[simp] theorem mem_horizontalCrossingEvent {a b c d : ℤ}
    {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ horizontalCrossingEvent a b c d ↔ HorizontalCrossing ω a b c d := Iff.rfl

@[simp] theorem mem_verticalCrossingEvent {a b c d : ℤ}
    {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ verticalCrossingEvent a b c d ↔ VerticalCrossing ω a b c d := Iff.rfl


theorem HorizontalCrossing.connected {a b c d : ℤ} {ω : ConfigSpace (Sym2 (Site 2))}
    (h : HorizontalCrossing ω a b c d) :
    ∃ x y : Site 2, x ∈ leftSide a b c d ∧ y ∈ rightSide a b c d ∧ Connected 2 ω x y := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, x.2, y.2, hxy.connected⟩


theorem VerticalCrossing.connected {a b c d : ℤ} {ω : ConfigSpace (Sym2 (Site 2))}
    (h : VerticalCrossing ω a b c d) :
    ∃ x y : Site 2, x ∈ bottomSide a b c d ∧ y ∈ topSide a b c d ∧ Connected 2 ω x y := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, x.2, y.2, hxy.connected⟩


theorem horizontalCrossingEvent_increasing {a b c d : ℤ}
    {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    (hω : ω ∈ horizontalCrossingEvent a b c d) :
    ω' ∈ horizontalCrossingEvent a b c d := by
  obtain ⟨x, y, hxy⟩ := hω
  exact ⟨x, y, connectedWithin_mono h hxy⟩


theorem verticalCrossingEvent_increasing {a b c d : ℤ}
    {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    (hω : ω ∈ verticalCrossingEvent a b c d) :
    ω' ∈ verticalCrossingEvent a b c d := by
  obtain ⟨x, y, hxy⟩ := hω
  exact ⟨x, y, connectedWithin_mono h hxy⟩


theorem horizontalCrossing_eq_twoDim (ω : ConfigSpace (Sym2 (Site 2))) (a b : ℤ) :
    HorizontalCrossing ω 0 a 0 b ↔ TwoDim.HorizontalCrossing ω a b := by
  have hrect : rect 0 a 0 b = TwoDim.rectangle a b := rfl
  rfl


end Box
end RSW
end StatMech
