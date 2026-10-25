/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.euceuler.Part3
import Theorem.StatisticalMechanics.Code.Walls.wadangledefect.Part3
open scoped BigOperators
open Finset
open StatMech.Euc


namespace StatMech.Wad

def wad_n1 (K : Finset Cell) : ℤ :=
  ((regVerts K).filter (fun v => defect K v = 1)).card

def wad_n3 (K : Finset Cell) : ℤ :=
  ((regVerts K).filter (fun v => defect K v = -1)).card

def wad_n2d (K : Finset Cell) : ℤ :=
  ((regVerts K).filter (fun v => defect K v = -2)).card


end StatMech.Wad
