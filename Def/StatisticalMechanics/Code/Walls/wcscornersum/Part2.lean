module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.wadangledefect.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
public import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
public import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle.Part2
public import Theorem.StatisticalMechanics.Code.Walls.wcscornersum
open scoped BigOperators
open Finset
open SimpleGraph Function


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wcscornersum.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Wcs

open StatMech.Lattice

open StatMech.Wad

open StatMech.Euc

open StatMech.Walls


def toVtxSet (K : Set (Site 2)) : Set (ℤ × ℤ) := siteToVtx '' K

end Wcs
end StatMech
