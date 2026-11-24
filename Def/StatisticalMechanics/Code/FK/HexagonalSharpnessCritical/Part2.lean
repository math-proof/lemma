module
public import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessThreshold
public import Theorem.StatisticalMechanics.Code.FK.HexagonalTranslatedArm.Part4
public import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
public import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
public import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessCritical
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


def hexagonalBufferedInnerShellEvent (k : Nat) :
    Set (ConfigSpace (Sym2 (hexagonal.BufferedVertex (2 * k)))) :=
  ocd_innerRestrict (hexagonalBoxToBuffered k) ⁻¹'
    hexagonalCenteredShellFullEvent (2 * k) k

end StatMech.FK.PeriodicPlanar
