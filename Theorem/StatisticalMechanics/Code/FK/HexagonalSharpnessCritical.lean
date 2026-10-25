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
import Def.StatisticalMechanics.Code.FK.HexagonalSharpnessCritical
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


theorem hexagonalBoxToBuffered_injective (k : Nat) :
    Function.Injective (hexagonalBoxToBuffered k) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : hexagonal.BufferedVertex (2 * k) => (z : HexVertex)) h

theorem hexagonalBoxToBuffered_adjMatch (k : Nat) :
    ocd_AdjMatch (hexagonalBoxGraph (2 * k))
      (hexagonal.bufferedGraph (2 * k)) (hexagonalBoxToBuffered k) := by
  intro x y
  rfl


end StatMech.FK.PeriodicPlanar
