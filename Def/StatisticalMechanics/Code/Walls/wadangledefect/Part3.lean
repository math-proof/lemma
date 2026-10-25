/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wadangledefect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.euceuler.Part3
import Theorem.StatisticalMechanics.Code.Walls.wadangledefect.Part2
open scoped BigOperators
open Finset
open StatMech.Euc


namespace StatMech.Wad

def incidentEdgeR (v : Vtx) : Sym2 Vtx := s(v, (v.1 + 1, v.2))

def incidentEdgeL (v : Vtx) : Sym2 Vtx := s(v, (v.1 - 1, v.2))

def incidentEdgeU (v : Vtx) : Sym2 Vtx := s(v, (v.1, v.2 + 1))

def incidentEdgeD (v : Vtx) : Sym2 Vtx := s(v, (v.1, v.2 - 1))


end StatMech.Wad
