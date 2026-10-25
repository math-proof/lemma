/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc53harmbox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc52jordanbridge.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
open Set SimpleGraph Finset
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc53_canonicalArm_inbox {ω : ConfigSpace (Sym2 (Site d))} {n : ℕ} {x a : Site d}
    (hx : x ∈ box d n) (hadj : (openSubgraph d ω).Adj x a) : a ∈ box d (n + 1) :=
  arc_neighbour_in_box_succ hx hadj.1


theorem bc53_canonicalArm_crosses_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x a : Site d) (hax : a ≠ x) (habox : a ∈ box d (n + 1))
    (hinf : (cluster d (removeSite x ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d (n + 1),
      ∃ w : (openSubgraph d (removeSite x ω)).Walk a z, x ∉ w.support :=
  arc_infinite_cluster_reaches_boundary ω (n + 1) (by omega) x a hax habox hinf


theorem bc53_harmbox_succ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite →
        a ∈ box d (n + 1) := by
  intro x hx _ a hadj _
  exact bc53_canonicalArm_inbox hx hadj


namespace Bc53Witness

open StatMech.Percolation.CtcWitness


theorem threeRay_canonical_origin :
    IsCanonicalTrifurcation 2 threeRayConfig (px 0) := by
  classical
  refine ⟨px 1, py 1, px (-1), ?_, ?_, ?_, ?_⟩
  · 
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have hc : (px 1) 1 = (py 1) 1 := by rw [h]
      simp [px, py] at hc
    · intro h; have h0 : (1 : ℤ) = -1 := px_inj h; omega
    · intro h
      have hc : (py 1) 0 = (px (-1)) 0 := by rw [h]
      simp [px, py] at hc
  · 
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨px_adj 0, ?_⟩
      have := px_ray_open 0; simpa [px] using this
    · refine ⟨py_adj 0, ?_⟩
      have := py_ray_open 0 (le_refl 0); simpa [py] using this
    · refine ⟨?_, ?_⟩
      · rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [px]
      · have := px_ray_open (-1)
        rw [show ((-1 : ℤ) + 1) = 0 by ring] at this
        rw [Sym2.eq_swap]; simpa [px] using this
  · 
    exact ⟨cut_px_pos_infinite, cut_py_pos_infinite, cut_px_neg_infinite⟩
  · 
    exact ⟨cut_disconnect_pos_py, cut_disconnect_pos_neg, fun h =>
      cut_disconnect_neg_py h.symm⟩


end Bc53Witness
end StatMech.Walls
