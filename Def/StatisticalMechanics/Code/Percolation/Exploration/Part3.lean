/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part2
open MeasureTheory Function Set
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice


variable {d : ℕ}


def clusterWithin (d : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (S : Set (Site d)) (o : Site d) :
    Set (Site d) :=
  {y | ∃ (hy : y ∈ S) (ho : o ∈ S), ConnectedWithin d ω S ⟨o, ho⟩ ⟨y, hy⟩}


def incidentWithin (K S : Set (Site d)) : Set (Sym2 (Site d)) :=
  {e | ∃ x ∈ K, ∃ y ∈ S, e = s(x, y)}

end Percolation
end StatMech
