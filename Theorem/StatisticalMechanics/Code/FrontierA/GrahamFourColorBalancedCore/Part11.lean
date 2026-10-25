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
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part12
open scoped BigOperators symmDiff
open Finset


namespace StatMech

namespace GrahamGHS

open Ising

open Sharpness


namespace FourColor

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]


set_option maxHeartbeats 800000 in
theorem colorClasses_coloringOfRowData {m K P Q : Finset ι} (hKm : K ⊆ m)
    (hPK : P ⊆ K) (hQL : Q ⊆ m \ K) :
    colorClass m (coloringOfRowData m K P Q) 0 = P ∧
      colorClass m (coloringOfRowData m K P Q) 1 = K \ P ∧
      colorClass m (coloringOfRowData m K P Q) 2 = Q ∧
      colorClass m (coloringOfRowData m K P Q) 3 = (m \ K) \ Q := by
  classical
  have hPm : P ⊆ m := hPK.trans hKm
  have hQm : Q ⊆ m := hQL.trans Finset.sdiff_subset
  have hQK : Disjoint Q K := by
    rw [Finset.disjoint_left]
    intro i hiQ hiK
    exact (Finset.mem_sdiff.mp (hQL hiQ)).2 hiK
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i
  all_goals
    have hKm_i := @hKm i
    have hPK_i := @hPK i
    have hQL_i := @hQL i
    have hPm_i := @hPm i
    have hQm_i := @hQm i
    by_cases him : i ∈ m <;> by_cases hiK : i ∈ K <;>
      by_cases hiP : i ∈ P <;> by_cases hiQ : i ∈ Q <;>
        simp [colorClass, coloringOfRowData, him, hiK, hiP, hiQ] at hKm_i hPK_i hQL_i hPm_i hQm_i hQK ⊢

theorem rowClasses_coloringOfRowData {m K P Q : Finset ι} (hKm : K ⊆ m)
    (hPK : P ⊆ K) (hQL : Q ⊆ m \ K) :
    rowClass m (coloringOfRowData m K P Q) 0 = K ∧
      rowClass m (coloringOfRowData m K P Q) 1 = m \ K := by
  have hc := colorClasses_coloringOfRowData hKm hPK hQL
  constructor
  · rw [rowClass_zero, hc.1, hc.2.1, Finset.union_sdiff_of_subset hPK]
  · rw [rowClass_one, hc.2.2.1, hc.2.2.2]
    exact Finset.union_sdiff_of_subset hQL

theorem rowClass_balancedSwap_one {m X Y : Finset ι} {c : ↑m → Fin 4}
    (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
    (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3) :
    rowClass m (balancedSwap m X Y c) 1 = rowClass m c 1 ∆ (X ∪ Y) := by
  rw [rowClass_one_eq_sdiff, rowClass_one_eq_sdiff,
    rowClass_balancedSwap_zero hX hY]
  have hXY : X ∪ Y ⊆ m := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · rcases Finset.mem_union.mp (hX hi) with hi | hi
      · exact colorClass_subset m c 1 hi
      · exact colorClass_subset m c 2 hi
    · rcases Finset.mem_union.mp (hY hi) with hi | hi
      · exact colorClass_subset m c 0 hi
      · exact colorClass_subset m c 3 hi
  ext i
  have hiXYm : i ∈ X ∪ Y → i ∈ m := fun hi => hXY hi
  by_cases him : i ∈ m <;>
    by_cases hir : i ∈ rowClass m c 0 <;>
      by_cases hiXY : i ∈ X ∪ Y <;>
        simp [Finset.mem_symmDiff, him, hir, hiXY] at hiXYm ⊢


end FourColor
end GrahamGHS
end StatMech
