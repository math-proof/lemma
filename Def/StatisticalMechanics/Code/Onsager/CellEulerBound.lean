module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.CellEuler.Part3
public import Theorem.StatisticalMechanics.Code.Walls.wadangledefect.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerBound.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager.CellEulerBound

open Finset SimpleGraph

open StatMech.Euc StatMech.Wad

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler


def edgeCode : Sym2 (ℤ × ℤ) → ℤ × ℤ :=
  Sym2.lift ⟨fun a b => (a.1 + b.1, a.2 + b.2), by
    intro a b
    ext <;> simp only <;> omega⟩

end StatMech.Onsager.CellEulerBound
