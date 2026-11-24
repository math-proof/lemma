module
public import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessThreshold
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
public import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
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


def triangularBoxToBuffered (k : Nat) :
    TriangularBoxVertex (2 * k) → triangular.BufferedVertex (2 * k) :=
  fun x => ⟨x.1, by
    rw [triangular_mem_orbitBox_iff_box]
    exact box_mono 2 (triangular.id_le_bufferedRadius (2 * k)) x.2⟩

end StatMech.FK.PeriodicPlanar
