/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalTranslatedArm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessThreshold
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Theorem.StatisticalMechanics.Code.FK.HexagonalTranslatedArm.Part2
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation

noncomputable def hexagonalTransBoxToBufferedAt (k : Nat) (x : Site 2) (m : Nat)
    (hm : hexagonalTransBufferLevel k x ≤ m) :
    HexagonalTransBoxVertex (2 * k) x → hexagonal.BufferedVertex m :=
  fun y => hexagonal.bufferedVertexInclLE hm
    (hexagonalTransBoxToBuffered k x y)

end StatMech.FK.PeriodicPlanar
