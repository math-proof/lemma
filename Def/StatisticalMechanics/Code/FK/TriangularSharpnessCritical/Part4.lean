module
public import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessThreshold
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
public import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
public import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessCritical.Part3
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean -/
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


def triangularBufferedToBox (j N : Nat)
    (hjn : triangular.bufferedRadius j ≤ 2 * N) :
    triangular.BufferedVertex j → TriangularBoxVertex (2 * N) :=
  fun x => ⟨x.1, by
    rw [← triangular_mem_orbitBox_iff_box]
    exact triangular.orbitBox_mono hjn x.2⟩

end StatMech.FK.PeriodicPlanar
