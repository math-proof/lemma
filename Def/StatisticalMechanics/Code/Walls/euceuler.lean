/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Abbrev.StatisticalMechanics.Code.Walls.euceuler
open scoped BigOperators
open Finset


namespace StatMech.Euc

def cellVerts (c : Cell) : Finset Vtx :=
  {(c.1, c.2), (c.1 + 1, c.2), (c.1, c.2 + 1), (c.1 + 1, c.2 + 1)}


def cellEdges (c : Cell) : Finset (Sym2 Vtx) :=
  { s((c.1, c.2), (c.1 + 1, c.2)),          
    s((c.1, c.2 + 1), (c.1 + 1, c.2 + 1)),  
    s((c.1, c.2), (c.1, c.2 + 1)),          
    s((c.1 + 1, c.2), (c.1 + 1, c.2 + 1)) } 


def regVerts (K : Finset Cell) : Finset Vtx := K.biUnion cellVerts


def regEdges (K : Finset Cell) : Finset (Sym2 Vtx) := K.biUnion cellEdges


def regChi (K : Finset Cell) : ℤ :=
  (regVerts K).card - (regEdges K).card + K.card


end StatMech.Euc
