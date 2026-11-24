module
public import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessThreshold
public import Theorem.StatisticalMechanics.Code.FK.HexagonalTranslatedArm.Part4
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
public import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
public import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessCritical.Part2
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


def hexagonalBoxToBufferedAt (k m : Nat)
    (hkm : 2 * k ≤ hexagonal.bufferedRadius m) :
    HexagonalBoxVertex (2 * k) → hexagonal.BufferedVertex m :=
  fun x => ⟨x.1, by
    rw [hexagonal_mem_orbitBox_iff_box]
    exact box_mono 2 hkm x.2.1⟩

end StatMech.FK.PeriodicPlanar
