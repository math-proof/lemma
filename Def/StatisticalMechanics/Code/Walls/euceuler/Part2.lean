/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/euceuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.euceuler
open scoped BigOperators
open Finset


namespace StatMech.Euc

def newVerts (c : Cell) (K : Finset Cell) : ℕ := (cellVerts c \ regVerts K).card


def newEdges (c : Cell) (K : Finset Cell) : ℕ := (cellEdges c \ regEdges K).card


end StatMech.Euc
