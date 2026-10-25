/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/earremovable.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Walls.nbcnoncut.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc_leafremoval.Part2
import Theorem.StatisticalMechanics.Code.Walls.atcattachstep.Part2
import Structure.StatisticalMechanics.Code.Walls.earremovable
open Finset Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem ear_exists_globalExtreme (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ c, ear_IsGlobalExtreme K c := by
  have hfne : hK.toFinset.Nonempty := by rwa [Set.Finite.toFinset_nonempty]
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image hK.toFinset ear_gKey hfne
  refine ⟨c, ⟨by rwa [Set.Finite.mem_toFinset] at hc, ?_⟩⟩
  intro v hv
  exact hmax v (by rwa [Set.Finite.mem_toFinset])


theorem ear_globalExtreme_not_mem_of_higher (K : Set (Site 2)) (c v : Site 2)
    (hc : ear_IsGlobalExtreme K c) (hy : c 1 < v 1) : v ∉ K := by
  intro hv
  have h := hc.maximal v hv
  unfold ear_gKey at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h1, h2⟩ <;> omega


theorem ear_globalExtreme_not_mem_of_right (K : Set (Site 2)) (c v : Site 2)
    (hc : ear_IsGlobalExtreme K c) (hy : v 1 = c 1) (hx : c 0 < v 0) : v ∉ K := by
  intro hv
  have h := hc.maximal v hv
  unfold ear_gKey at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h1, h2⟩ <;> omega


theorem ear_globalExtreme_up_nmem (K : Set (Site 2)) (c : Site 2)
    (hc : ear_IsGlobalExtreme K c) : c + ![0, 1] ∉ K := by
  apply ear_globalExtreme_not_mem_of_higher K c _ hc; simp [Pi.add_apply]


theorem ear_globalExtreme_right_nmem (K : Set (Site 2)) (c : Site 2)
    (hc : ear_IsGlobalExtreme K c) : c + ![1, 0] ∉ K := by
  apply ear_globalExtreme_not_mem_of_right K c _ hc <;> simp [Pi.add_apply]


theorem ear_globalExtreme_boundary (K : Set (Site 2)) (c : Site 2)
    (hc : ear_IsGlobalExtreme K c) : ∃ n ∉ K, (hypercubicLattice 2).Adj c n := by
  refine ⟨c + ![0, 1], ear_globalExtreme_up_nmem K c hc, ?_⟩
  rw [hypercubicLattice_adj, Fin.sum_univ_two]
  simp [Pi.add_apply]


theorem ear_globalExtreme_neighbor_left_or_down (K : Set (Site 2)) (c v : Site 2)
    (hc : ear_IsGlobalExtreme K c) (hv : v ∈ K) (hadj : (hypercubicLattice 2).Adj v c) :
    v = c + ![-1, 0] ∨ v = c + ![0, -1] := by
  rcases adj_neighbor_cases v c hadj with h | h | h | h
  · exact absurd (h ▸ hv) (ear_globalExtreme_right_nmem K c hc)
  · exact Or.inl h
  · exact absurd (h ▸ hv) (ear_globalExtreme_up_nmem K c hc)
  · exact Or.inr h


end Walls
end StatMech
