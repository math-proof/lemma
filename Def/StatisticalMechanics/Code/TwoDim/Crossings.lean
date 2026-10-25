/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
open Set


namespace StatMech

namespace TwoDim

open StatMech.Lattice

variable {a b : ℤ}


def rectangle (a b : ℤ) : Set (Site 2) :=
  {x | 0 ≤ x 0 ∧ x 0 ≤ a ∧ 0 ≤ x 1 ∧ x 1 ≤ b}

end TwoDim
end StatMech
