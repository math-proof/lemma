/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalTranslatedArm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessThreshold
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Theorem.StatisticalMechanics.Code.FK.HexagonalTranslatedArm.Part3
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation

def hexagonalBufferedTransShellEvent (k : Nat) (x : HexVertex) :
    Set (ConfigSpace (Sym2
      (hexagonal.BufferedVertex (hexagonalTransBufferLevel k x.1)))) :=
  ocd_innerRestrict (hexagonalTransBoxToBuffered k x.1) ⁻¹'
    hexagonalTransShellFullEvent (2 * k) k x

end StatMech.FK.PeriodicPlanar
