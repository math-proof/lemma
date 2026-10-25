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
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessCritical.Part4
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


noncomputable def hexagonalBufferedToBox (j N : Nat)
    (hjn : hexagonal.bufferedRadius j ≤ 2 * N) :
    hexagonal.BufferedVertex j → HexagonalBoxVertex (2 * N) :=
  fun x => ⟨hexagonalRootFrame x.1, by
    refine ⟨?_, Set.mem_univ _⟩
    rw [hexagonalRootFrame_coord_mem_box_iff]
    rw [← hexagonal_mem_orbitBox_iff_box]
    exact hexagonal.orbitBox_mono hjn x.2⟩

end StatMech.FK.PeriodicPlanar
