/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalTranslatedArm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessThreshold
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Theorem.StatisticalMechanics.Code.FK.HexagonalTranslatedArm
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation

def hexagonalTransBoxToBuffered (k : Nat) (x : Site 2) :
    HexagonalTransBoxVertex (2 * k) x →
      hexagonal.BufferedVertex (hexagonalTransBufferLevel k x) :=
  fun y => ⟨y.1, by
    rw [hexagonal_mem_orbitBox_iff_box]
    exact box_mono 2
      (hexagonal.id_le_bufferedRadius (hexagonalTransBufferLevel k x))
      (hexagonalTransBox_mem_bufferLevel k x y)⟩

end StatMech.FK.PeriodicPlanar
