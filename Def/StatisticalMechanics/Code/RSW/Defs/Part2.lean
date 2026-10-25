/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Theorem.StatisticalMechanics.Code.RSW.Defs
open Set


namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice

open StatMech.TwoDim


def leftSide (a b c d : ℤ) : Set (Site 2) := {x | x ∈ rect a b c d ∧ x 0 = a}


def rightSide (a b c d : ℤ) : Set (Site 2) := {x | x ∈ rect a b c d ∧ x 0 = b}


def bottomSide (a b c d : ℤ) : Set (Site 2) := {x | x ∈ rect a b c d ∧ x 1 = c}


def topSide (a b c d : ℤ) : Set (Site 2) := {x | x ∈ rect a b c d ∧ x 1 = d}

end Box
end RSW
end StatMech
