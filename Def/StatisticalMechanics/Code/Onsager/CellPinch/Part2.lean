module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.CellEuler.Part3
public import Instance.StatisticalMechanics.Code.Onsager.CellPinch


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellPinch.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager.CellPinch

open Finset StatMech.Onsager.CellCount StatMech.Onsager.CellEuler


def pinchW (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) : ℤ := if pinchAt S v then 1 else 0


def pinchCount (S : Finset (ℤ × ℤ)) : ℤ := ∑ v ∈ cellVerts S, pinchW S v


end StatMech.Onsager.CellPinch
