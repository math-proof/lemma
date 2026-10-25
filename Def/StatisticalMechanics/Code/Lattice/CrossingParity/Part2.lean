/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossingParity.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

noncomputable def latticeMinusBarrier (S : Set (Site 2)) : SimpleGraph (Site 2) where
  Adj x y := (hypercubicLattice 2).Adj x y ∧ ¬ bdEdge S s(x, y)
  symm := by
    constructor
    intro x y ⟨hadj, hbd⟩
    refine ⟨hadj.symm, ?_⟩
    rwa [Sym2.eq_swap]
  loopless := ⟨fun x h => (hypercubicLattice 2).irrefl h.1⟩

end Lattice
end StatMech
