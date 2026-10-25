/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.euceuler.Part3
open scoped BigOperators
open Finset
open StatMech.Euc


namespace StatMech.Wad

def surroundCells (v : Vtx) : Finset Cell :=
  {(v.1 - 1, v.2 - 1), (v.1, v.2 - 1), (v.1 - 1, v.2), (v.1, v.2)}


def cellDeg (K : Finset Cell) (v : Vtx) : ℕ := (surroundCells v ∩ K).card


def edgeDeg (K : Finset Cell) (v : Vtx) : ℕ :=
  ((regEdges K).filter (fun e => v ∈ e)).card


end StatMech.Wad
