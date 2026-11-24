module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Onsager.WalkCellBoundary
public import Theorem.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part8
public import Theorem.StatisticalMechanics.Code.Onsager.CellEulerFaithful.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEulerFaithful.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager.CellEulerFaithful

open Finset SimpleGraph Set

open StatMech.Lattice StatMech.Euc StatMech.Wad

open StatMech.Onsager.CellCount StatMech.Onsager.CellEuler
  StatMech.Onsager.CellEulerBound StatMech.Onsager.WalkCellRegion
  StatMech.Onsager.WalkCellBoundary StatMech.Onsager.BaseCase


noncomputable def occupiedBoundedFace (S : Finset Cell) (c : S) :
    jcb_BoundedRegion (cellSkeletonP S) :=
  ⟨occupiedComponent S c.1, occupiedComponent_finite S c.1 c.2⟩

end StatMech.Onsager.CellEulerFaithful
