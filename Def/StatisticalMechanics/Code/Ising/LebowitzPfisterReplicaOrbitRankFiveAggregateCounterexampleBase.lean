/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveCounterexample
import Abbrev.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateCounterexampleBase
open Finset
open scoped symmDiff


namespace StatMech.Ising.LPRankFiveAggregateCounterexample

open LPRankFiveCounterexample

def seam : Seam -> Finset LPRankFiveCounterVertex
  | 0 => seamI
  | 1 => seamJ
  | 2 => {6, 7}


def sourceSectorStates (i j : Seam) : Finset
    (LPRankFiveCounterOrientation × LPRankFiveCounterColoring) :=
  Finset.univ.filter fun z =>
    pattern z.1 ∅ (seam i ∆ seam j ∆ ghosts) z.2


def targetSectorStates (i j : Seam) : Finset
    (LPRankFiveCounterOrientation × LPRankFiveCounterColoring) :=
  Finset.univ.filter fun z =>
    pattern z.1 (seam i) (seam j ∆ ghosts) z.2


def sectorOrientations : Seam -> Seam ->
    Finset LPRankFiveCounterOrientation
  | 0, 0 => {4, 11}
  | 0, 1 => {0, 15}
  | 0, 2 => {6, 9}
  | 1, 0 => {0, 15}
  | 1, 1 => {4, 11}
  | 1, 2 => {2, 13}
  | 2, 0 => {6, 9}
  | 2, 1 => {2, 13}
  | 2, 2 => {4, 11}


def targetColoring : LPRankFiveCounterColoring := ⟨170, by decide⟩

end StatMech.Ising.LPRankFiveAggregateCounterexample
