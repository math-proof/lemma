/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceClusterUniqueness
import Theorem.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part4
import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence.Part4
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceCanonicalRouting.Part2
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierB

open Lattice ConfigSpace Percolation

open Percolation.DisjointPaths

variable {d : ℕ}


def HubCorridorWorks (z a₁ a₂ a₃ : Site d)
    (G : Finset (Sym2 (Site d))) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {ω | (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
    ((hypercubicLattice d).Adj z a₁ ∧
      (hypercubicLattice d).Adj z a₂ ∧
      (hypercubicLattice d).Adj z a₃) ∧
    ((cluster d (removeSite z (forceOpenFinset G ω)) a₁).Infinite ∧
      (cluster d (removeSite z (forceOpenFinset G ω)) a₂).Infinite ∧
      (cluster d (removeSite z (forceOpenFinset G ω)) a₃).Infinite) ∧
    (cluster d (removeSite z (forceOpenFinset G ω)) a₁ ≠
        cluster d (removeSite z (forceOpenFinset G ω)) a₂ ∧
      cluster d (removeSite z (forceOpenFinset G ω)) a₁ ≠
        cluster d (removeSite z (forceOpenFinset G ω)) a₃ ∧
      cluster d (removeSite z (forceOpenFinset G ω)) a₂ ≠
        cluster d (removeSite z (forceOpenFinset G ω)) a₃)}


end StatMech.FrontierB
