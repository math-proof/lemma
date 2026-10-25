/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePropsFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Theorem.StatisticalMechanics.Code.Walls.vbgtriangle.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc7ghosteven
import Instance.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part3
open scoped BigOperators symmDiff
open Finset


namespace StatMech

namespace GrahamGHS

open Ising

open Sharpness


namespace FourColor

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]


noncomputable def leftFiberToRowData (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : leftFiber ends m {j, k} {k, l} k zero →
      leftRowData ends m j k l zero := fun c => by
  classical
  let K := rowClass m c.1 0
  have hKm : K ⊆ m := by
    intro i hi
    dsimp only [K] at hi
    rw [rowClass_zero, Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact colorClass_subset m c.1 0 hi
    · exact colorClass_subset m c.1 1 hi
  have hrows := leftPattern_rowBoundaries c.2
  have hsupport : LeftRowSupport ends m j k l zero K := by
    unfold LeftRowSupport
    have hrow1 : m \ K = rowClass m c.1 1 := by
      dsimp only [K]
      rw [rowClass_one_eq_sdiff]
    exact ⟨hrows.1, hrow1 ▸ hrows.2, c.2.2.2.2.2.1,
      hrow1 ▸ c.2.2.2.2.2.2⟩
  have hC0 : colorClass m c.1 0 ⊆ K := by
    dsimp only [K]
    rw [rowClass_zero]
    exact Finset.subset_union_left
  have hC2 : colorClass m c.1 2 ⊆ m \ K := by
    dsimp only [K]
    rw [← rowClass_one_eq_sdiff, rowClass_one]
    exact Finset.subset_union_left
  exact ⟨⟨K, hKm, hsupport⟩,
    ⟨⟨colorClass m c.1 0, hC0, c.2.1⟩,
      ⟨colorClass m c.1 2, hC2, c.2.2.2.1⟩⟩⟩

noncomputable def rowDataToLeftFiber (ends : ι → Sym2 W) (m : Finset ι)
    (j k l zero : W) : leftRowData ends m j k l zero →
      leftFiber ends m {j, k} {k, l} k zero := fun d => by
  classical
  let K := d.1.1
  let P := d.2.1.1
  let Q := d.2.2.1
  let c := coloringOfRowData m K P Q
  have hc := colorClasses_coloringOfRowData d.1.2.1 d.2.1.2.1 d.2.2.2.1
  have hr := rowClasses_coloringOfRowData d.1.2.1 d.2.1.2.1 d.2.2.2.1
  refine ⟨c, ?_⟩
  unfold LeftPattern
  change Sharpness.RandomCurrent.sources ends (colorClass m c 0) = {j, k} ∧
    Sharpness.RandomCurrent.sources ends (colorClass m c 1) = ∅ ∧
    Sharpness.RandomCurrent.sources ends (colorClass m c 2) = {k, l} ∧
    Sharpness.RandomCurrent.sources ends (colorClass m c 3) = ∅ ∧
    RowsDisconnect ends m c k zero
  have hs := d.1.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hc.1]
    exact d.2.1.2.2
  · rw [hc.2.1, sources_sdiff_of_subset d.2.1.2.1, hs.1, d.2.1.2.2,
      symmDiff_self]
    rfl
  · rw [hc.2.2.1]
    exact d.2.2.2.2
  · rw [hc.2.2.2, sources_sdiff_of_subset d.2.2.2.1, hs.2.1, d.2.2.2.2,
      symmDiff_self]
    rfl
  · rw [RowsDisconnect, hr.1, hr.2]
    exact ⟨hs.2.2.1, hs.2.2.2⟩

end FourColor
end GrahamGHS
end StatMech
