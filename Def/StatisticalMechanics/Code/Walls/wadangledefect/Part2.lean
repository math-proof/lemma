/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.euceuler.Part3
import Theorem.StatisticalMechanics.Code.Walls.wadangledefect
open scoped BigOperators
open Finset
open StatMech.Euc


namespace StatMech.Wad

def defect (K : Finset Cell) (v : Vtx) : ℤ :=
  4 - 2 * (edgeDeg K v : ℤ) + (cellDeg K v : ℤ)


end StatMech.Wad
