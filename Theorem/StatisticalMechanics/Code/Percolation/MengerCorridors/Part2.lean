/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerCorridors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneAttachment.Part4
import Def.StatisticalMechanics.Code.Percolation.MengerCorridors
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem mco_mergeFree (ω : ConfigSpace (Sym2 (Site d)))
    (h : mco_ThreeClustersReachOrigin ω) : bka_MergeFree ω := by
  obtain ⟨a₁, a₂, a₃, x₁, x₂, x₃, hadj, hconn, hinf, hdist⟩ := h
  exact mco_mergeFree_of_reach ω a₁ a₂ a₃ x₁ x₂ x₃ hadj hconn hinf hdist


theorem mco_distinct_clusters_residue (ω : ConfigSpace (Sym2 (Site d)))
    (h : mco_ThreeClustersReachOrigin ω) : bcc_distinct_clusters_residue ω :=
  bka_distinct_clusters ω (mco_mergeFree ω h)


theorem mco_disjointRouting (ω : ConfigSpace (Sym2 (Site d)))
    (h : mco_ThreeClustersReachOrigin ω) : DisjointPaths.DisjointCorridorRouting ω :=
  bka_disjointRouting_of_mergeFree ω (mco_mergeFree ω h)


theorem mco_routing (n : ℕ)
    (hreach : ∀ ω ∈ threeMeetBox d n, mco_ThreeClustersReachOrigin ω) :
    hrHD_DisjointRouting d n :=
  bka_routing_of_mergeFree n (fun ω hω => mco_mergeFree ω (hreach ω hω))


end Percolation
end StatMech
