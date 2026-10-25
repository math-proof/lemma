/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part2


namespace StatMech.Universality

open HexWalk


def HLHAAwayDir (d : HexReturnCoord) : Prop :=
  d = ⟨1, 1⟩ ∨ d = ⟨0, 1⟩ ∨ d = ⟨-1, 0⟩ ∨ d = ⟨-1, -1⟩


def hlha_useSwap (d : HexReturnCoord) : Bool :=
  decide (d = ⟨0, 1⟩ ∨ d = ⟨-1, -1⟩)


def hlha_cutTurn (d : HexReturnCoord) : ℤ :=
  if d = ⟨0, 1⟩ ∨ d = ⟨-1, 0⟩ then 1 else -1

def hlha_normCoord (d p : HexReturnCoord) : HexReturnCoord :=
  if hlha_useSwap d then hlha_swapCoord p else hlha_negCoord p

def hlha_normTurns (d : HexReturnCoord) (ts : List ℤ) : List ℤ :=
  if hlha_useSwap d then hsc_negTurns ts else ts


def hlha_augmentSide (d : HexReturnCoord) (internal : List ℤ) : List ℤ :=
  -1 :: hlha_cutTurn d :: hlha_normTurns d internal

def hlha_outerStep : HexReturnCoord :=
  HexReturnCoord.base.turn (-1)

end StatMech.Universality
