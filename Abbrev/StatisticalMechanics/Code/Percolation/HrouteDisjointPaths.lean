/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

namespace DisjointPaths

variable {d : ℕ}


abbrev CorridorStep (G : Finset (Sym2 (Site d))) (u v : Site d) : Prop :=
  (hypercubicLattice d).Adj u v ∧ s(u, v) ∈ G ∧ (0 : Site d) ∉ s(u, v)


end DisjointPaths
end Percolation
end StatMech
