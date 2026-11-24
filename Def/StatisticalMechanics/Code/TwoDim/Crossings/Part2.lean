module
public import Mathlib
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.TwoDim.Crossings
open Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace TwoDim

open StatMech.Lattice

variable {a b : ℤ}


def leftSide (a b : ℤ) : Set (Site 2) := {x | x ∈ rectangle a b ∧ x 0 = 0}


def rightSide (a b : ℤ) : Set (Site 2) := {x | x ∈ rectangle a b ∧ x 0 = a}


def bottomSide (a b : ℤ) : Set (Site 2) := {x | x ∈ rectangle a b ∧ x 1 = 0}


def topSide (a b : ℤ) : Set (Site 2) := {x | x ∈ rectangle a b ∧ x 1 = b}

end TwoDim
end StatMech
