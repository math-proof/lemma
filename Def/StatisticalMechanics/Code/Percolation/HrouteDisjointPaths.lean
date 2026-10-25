/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

namespace DisjointPaths

variable {d : ℕ}


def CorridorWorks (a₁ a₂ a₃ : Site d) (G : Finset (Sym2 (Site d))) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃) ∧
    ((cluster d (removeSite 0 (forceOpenFinset G ω)) a₁).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) a₂).Infinite ∧
      (cluster d (removeSite 0 (forceOpenFinset G ω)) a₃).Infinite) ∧
    (cluster d (removeSite 0 (forceOpenFinset G ω)) a₁
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₂ ∧
      cluster d (removeSite 0 (forceOpenFinset G ω)) a₁
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₃ ∧
      cluster d (removeSite 0 (forceOpenFinset G ω)) a₂
        ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₃)}


end DisjointPaths
end Percolation
end StatMech
