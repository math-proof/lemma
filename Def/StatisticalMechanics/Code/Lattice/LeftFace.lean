/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LeftFace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


def leftAxisSite (k : ℕ) : Site 2 := ![-(k : ℤ), 0]

end Lattice
end StatMech
