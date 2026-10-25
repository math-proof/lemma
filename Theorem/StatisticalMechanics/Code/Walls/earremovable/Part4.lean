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
import Structure.StatisticalMechanics.Code.Walls.earremovable.Part2
open Finset Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice

open StatMech.Ising (IsConnectedCluster origin latticeOn)

attribute [local instance] Classical.propDecidable


theorem ear_exists_antiExtreme (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ b, ear_IsAntiExtreme K b := by
  have hfne : hK.toFinset.Nonempty := by rwa [Set.Finite.toFinset_nonempty]
  obtain ⟨b, hb, hmin⟩ := Finset.exists_min_image hK.toFinset ear_gKey hfne
  refine ⟨b, ⟨by rwa [Set.Finite.mem_toFinset] at hb, ?_⟩⟩
  intro v hv
  exact hmin v (by rwa [Set.Finite.mem_toFinset])


theorem ear_antiExtreme_not_mem_of_lower (K : Set (Site 2)) (b v : Site 2)
    (hb : ear_IsAntiExtreme K b) (hy : v 1 < b 1) : v ∉ K := by
  intro hv
  have h := hb.minimal v hv
  unfold ear_gKey at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h1, h2⟩ <;> omega


theorem ear_antiExtreme_not_mem_of_left (K : Set (Site 2)) (b v : Site 2)
    (hb : ear_IsAntiExtreme K b) (hy : v 1 = b 1) (hx : v 0 < b 0) : v ∉ K := by
  intro hv
  have h := hb.minimal v hv
  unfold ear_gKey at h
  rw [Prod.Lex.toLex_le_toLex] at h
  rcases h with h | ⟨h1, h2⟩ <;> omega


theorem ear_antiExtreme_down_nmem (K : Set (Site 2)) (b : Site 2)
    (hb : ear_IsAntiExtreme K b) : b + ![0, -1] ∉ K := by
  apply ear_antiExtreme_not_mem_of_lower K b _ hb; simp [Pi.add_apply]


theorem ear_antiExtreme_left_nmem (K : Set (Site 2)) (b : Site 2)
    (hb : ear_IsAntiExtreme K b) : b + ![-1, 0] ∉ K := by
  apply ear_antiExtreme_not_mem_of_left K b _ hb <;> simp [Pi.add_apply]


theorem ear_antiExtreme_boundary (K : Set (Site 2)) (b : Site 2)
    (hb : ear_IsAntiExtreme K b) : ∃ n ∉ K, (hypercubicLattice 2).Adj b n := by
  refine ⟨b + ![0, -1], ear_antiExtreme_down_nmem K b hb, ?_⟩
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [Pi.add_apply]


end Walls
end StatMech
