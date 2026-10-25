/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourClose.Part4
import Theorem.StatisticalMechanics.Code.Ising.PeierlsContourCount.Part2
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


noncomputable def latticeOn (K : Set (Site d)) : SimpleGraph (Site d) where
  Adj x y := (hypercubicLattice d).Adj x y ∧ x ∈ K ∧ y ∈ K
  symm := by constructor; intro x y ⟨h1, h2, h3⟩; exact ⟨h1.symm, h3, h2⟩
  loopless := ⟨fun x h => (hypercubicLattice d).irrefl h.1⟩


def IsConnectedCluster (K : Finset (Site d)) : Prop :=
  origin d ∈ K ∧ ∀ x ∈ K, (latticeOn (↑K : Set (Site d))).Reachable (origin d) x


noncomputable def connClusterFamily (n : ℕ) : Finset (Finset (Site d)) :=
  (clusterFamily (d := d) n).filter (fun K => IsConnectedCluster K)

end Ising
end StatMech
