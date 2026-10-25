/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc56menger.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc55route
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BoxMengerAttachment.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay.Part3
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


def bc56_ClusterReachesNbr (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  ∃ a : Site d,
    (hypercubicLattice d).Adj 0 a ∧
    a ∈ cluster d ω x ∧
    Connected d (removeSite 0 ω) a x ∧
    (cluster d (removeSite 0 ω) x).Infinite


end StatMech.Walls
