/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LastExit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Percolation.LastExit
open MeasureTheory Set SimpleGraph
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice


variable {d : ℕ}


def offClusterCrossing (d : ℕ) (C : Set (Site d)) (y : Site d) (n : ℕ)
    (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  ∃ v, v ∉ box d (n - 1) ∧ ∃ (hy : y ∉ C) (hv : v ∉ C),
    ConnectedWithin d ω {z | z ∉ C} ⟨y, hy⟩ ⟨v, hv⟩


def boundaryOpen (d : ℕ) (C : Set (Site d)) (x y : Site d)
    (ω : ConfigSpace (Sym2 (Site d))) : Prop :=
  x ∈ C ∧ y ∉ C ∧ IsOpenEdge d ω x y


end Percolation
end StatMech
