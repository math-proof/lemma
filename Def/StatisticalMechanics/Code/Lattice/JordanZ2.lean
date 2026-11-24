module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
open Finset Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanZ2.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

def faceCorner00 (a b : ℤ) : Site 2 := ![a, b]


def faceCorner10 (a b : ℤ) : Site 2 := ![a + 1, b]


def faceCorner11 (a b : ℤ) : Site 2 := ![a + 1, b + 1]


def faceCorner01 (a b : ℤ) : Site 2 := ![a, b + 1]


end Lattice
end StatMech
