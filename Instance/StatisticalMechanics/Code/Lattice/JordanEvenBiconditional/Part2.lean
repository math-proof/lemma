/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenBiconditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part8
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part2
open SimpleGraph Set


namespace StatMech

namespace Lattice

noncomputable instance jeb_imageGraph_fintypeEdgeSet (P : PlanarZ2Subgraph) :
    Fintype (imageGraph P).edgeSet := by
  classical
  apply Set.Finite.fintype
  have hsupp := jeb_imageGraph_support_finite P
  apply Set.Finite.subset (s := (hsupp.toFinset.sym2 : Set (Sym2 (Site 2))))
  · exact (hsupp.toFinset.sym2).finite_toSet
  · rw [Finset.coe_sym2]
    exact (SimpleGraph.edgeSet_subset_sym2_iff).mpr
      (fun v hv => by rw [Finset.mem_coe, Set.Finite.mem_toFinset]; exact hv)


end Lattice
end StatMech
