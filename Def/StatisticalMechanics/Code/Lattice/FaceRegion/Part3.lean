/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/FaceRegion.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}


def insideRegion (ω : ConfigSpace (Sym2 (Site 2))) (o : Site 2) : Set (Site 2) :=
  {x | (cutLattice (cluster 2 ω o)).Reachable o x}

end Lattice
end StatMech
