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
import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessCritical.Part7
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


def triangularTransBoxToBuffered (k : Nat) (x : Site 2) :
    TriangularTransBoxVertex (2 * k) x →
      triangular.BufferedVertex (triangularTransBufferLevel k x) :=
  fun y => ⟨y.1, by
    rw [triangular_mem_orbitBox_iff_box]
    exact box_mono 2
      (triangular.id_le_bufferedRadius (triangularTransBufferLevel k x))
      (triangularTransBox_mem_bufferLevel k x y)⟩

end StatMech.FK.PeriodicPlanar
