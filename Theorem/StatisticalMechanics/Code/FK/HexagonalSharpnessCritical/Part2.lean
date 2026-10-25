/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessThreshold
import Theorem.StatisticalMechanics.Code.FK.HexagonalTranslatedArm.Part4
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Def.StatisticalMechanics.Code.FK.HexagonalSharpnessCritical.Part2
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


theorem hexagonalCenteredShellFullEvent_increasing (R k : Nat) :
    IsIncreasing (hexagonalCenteredShellFullEvent R k) := by
  intro omega eta home hmem
  obtain ⟨y, hy, hreach⟩ := hmem
  refine ⟨y, hy, hreach.mono ?_⟩
  intro x z hxz
  rw [FK.openSub_adj] at hxz ⊢
  refine ⟨hxz.1, ?_⟩
  apply Bool.eq_true_of_true_le
  simpa [hxz.2] using home s(x, z)

theorem hexagonalBufferedInnerShellEvent_increasing (k : Nat) :
    IsIncreasing (hexagonalBufferedInnerShellEvent k) := by
  intro omega eta home hmem
  exact hexagonalCenteredShellFullEvent_increasing (2 * k) k
    (fun e => home _) hmem


end StatMech.FK.PeriodicPlanar
