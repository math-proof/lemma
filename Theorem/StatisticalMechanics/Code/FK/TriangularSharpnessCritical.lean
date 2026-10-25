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
import Def.StatisticalMechanics.Code.FK.TriangularSharpnessCritical
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


theorem triangularBoxToBuffered_injective (k : Nat) :
    Function.Injective (triangularBoxToBuffered k) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : triangular.BufferedVertex (2 * k) => (z : Site 2)) h

theorem triangularBoxToBuffered_adjMatch (k : Nat) :
    ocd_AdjMatch (triangularBoxGraph (2 * k))
      (triangular.bufferedGraph (2 * k)) (triangularBoxToBuffered k) := by
  intro x y
  rfl


end StatMech.FK.PeriodicPlanar
