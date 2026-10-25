/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosure.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

noncomputable def sharedPrimalEdge (f g : Site 2) : Sym2 (Site 2) := by
  classical
  exact if f 0 = g 0 then
    s(![f 0, max (f 1) (g 1)], ![f 0 + 1, max (f 1) (g 1)])
  else
    s(![max (f 0) (g 0), f 1], ![max (f 0) (g 0), f 1 + 1])


end Lattice
end StatMech
