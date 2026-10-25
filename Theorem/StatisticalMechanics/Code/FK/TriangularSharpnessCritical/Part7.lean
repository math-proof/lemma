/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessThreshold
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Def.StatisticalMechanics.Code.FK.TriangularSharpnessCritical.Part7
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


theorem triangularTransBox_mem_bufferLevel
    (k : Nat) (x : Site 2) (y : TriangularTransBoxVertex (2 * k) x) :
    y.1 ∈ box 2 (triangularTransBufferLevel k x) := by
  rw [mem_box_iff_siteRadius_le]
  have hrad : centeredRadius x y.1 ≤ 2 * k := by
    rw [centeredRadius, siteRadius_le_iff]
    exact y.2
  exact (siteRadius_triangle y.1 x).trans (Nat.add_le_add_left hrad _)

end StatMech.FK.PeriodicPlanar
