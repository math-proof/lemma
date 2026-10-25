/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.MengerCorridors.Part3
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem tre_removeSite_forceOpen_comm (W : Finset (Sym2 (Site d)))
    (hW : ∀ e ∈ W, (0 : Site d) ∉ e) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSite 0 (forceOpenFinset W ω) = forceOpenFinset W (removeSite 0 ω) := by
  funext e
  unfold removeSite forceOpenFinset
  by_cases hx : (0 : Site d) ∈ e
  · have hnW : e ∉ W := fun he => hW e he hx
    simp [hx, hnW]
  · by_cases heW : e ∈ W <;> simp [hx, heW]


theorem tre_removeSite_mono_forceOpen (W : Finset (Sym2 (Site d)))
    (hW : ∀ e ∈ W, (0 : Site d) ∉ e) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSite 0 ω ≤ removeSite 0 (forceOpenFinset W ω) := by
  rw [tre_removeSite_forceOpen_comm W hW]
  exact forceOpenFinset_le W (removeSite 0 ω)


theorem tre_cluster_infinite_of_omega (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (hW : ∀ e ∈ W, (0 : Site d) ∉ e) (x : Site d)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) :
    (cluster d (removeSite 0 (forceOpenFinset W ω)) x).Infinite :=
  hinf.mono (cluster_mono (tre_removeSite_mono_forceOpen W hW ω) x)


theorem tre_branch_infinite_of_reach (ω' : ConfigSpace (Sym2 (Site d))) (a x : Site d)
    (hc : Connected d (removeSite 0 ω') a x)
    (hinf : (cluster d (removeSite 0 ω') x).Infinite) :
    (cluster d (removeSite 0 ω') a).Infinite := by
  rw [cluster_eq_of_connected hc]; exact hinf


theorem tre_branch_distinct_of_regions (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (a b : Site d) (R S : Set (Site d))
    (haR : a ∈ R) (hbS : b ∈ S)
    (homR : ∀ u v, u ∈ R → IsOpenEdge d ω u v → v ∈ R)
    (hgR : ∀ u v, u ∈ R → s(u, v) ∈ W → v ∈ R)
    (homS : ∀ u v, u ∈ S → IsOpenEdge d ω u v → v ∈ S)
    (hgS : ∀ u v, u ∈ S → s(u, v) ∈ W → v ∈ S)
    (hdisj : Disjoint R S) :
    cluster d (removeSite 0 (forceOpenFinset W ω)) a
      ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) b := by
  set ϱ := removeSite (0 : Site d) (forceOpenFinset W ω) with hϱ
  have hRcl : ∀ u v, u ∈ R → (openSubgraph d ϱ).Adj u v → v ∈ R :=
    bka_region_rhoAdjClosed ω W R homR hgR
  have hScl : ∀ u v, u ∈ S → (openSubgraph d ϱ).Adj u v → v ∈ S :=
    bka_region_rhoAdjClosed ω W S homS hgS
  have hsubR : cluster d ϱ a ⊆ R := DisjointPaths.cluster_subset_of_adjClosed ϱ R a haR hRcl
  have hsubS : cluster d ϱ b ⊆ S := DisjointPaths.cluster_subset_of_adjClosed ϱ S b hbS hScl
  exact DisjointPaths.cluster_ne_of_disjoint ϱ a b R S hsubR hsubS hdisj


end Percolation
end StatMech
