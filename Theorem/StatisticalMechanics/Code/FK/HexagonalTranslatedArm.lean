/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalTranslatedArm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessThreshold
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Def.StatisticalMechanics.Code.FK.HexagonalTranslatedArm
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation

theorem hexagonalTransBox_mem_bufferLevel
    (k : Nat) (x : Site 2) (y : HexagonalTransBoxVertex (2 * k) x) :
    y.1.1 ∈ box 2 (hexagonalTransBufferLevel k x) := by
  rw [mem_box_iff_siteRadius_le]
  have hrad : centeredRadius x y.1.1 ≤ 2 * k := by
    rw [centeredRadius, siteRadius_le_iff]
    exact y.2.1
  exact (siteRadius_triangle y.1.1 x).trans (Nat.add_le_add_left hrad _)

end StatMech.FK.PeriodicPlanar
