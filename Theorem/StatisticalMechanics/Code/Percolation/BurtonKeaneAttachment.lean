/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.CorridorConfinement.Part2
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

open DisjointPaths

variable {d : ℕ}


theorem bka_far_witness (ω : ConfigSpace (Sym2 (Site d))) (w : Site d)
    (hinf : (cluster d ω w).Infinite) (n : ℕ) :
    ∃ y, y ∉ box d n ∧ Connected d ω w y :=
  (cluster_infinite_iff ω w).mp hinf n


theorem bka_exists_far_connected (ω : ConfigSpace (Sym2 (Site d))) (w : Site d)
    (hinf : (cluster d ω w).Infinite) (n : ℕ) :
    ∃ y ∈ cluster d ω w, y ∉ box d n := by
  obtain ⟨y, hyb, hyc⟩ := bka_far_witness ω w hinf n
  exact ⟨y, hyc, hyb⟩


theorem bka_isOpenEdge_survives (ω : ConfigSpace (Sym2 (Site d)))
    (G : Finset (Sym2 (Site d))) {x y : Site d}
    (hopen : IsOpenEdge d ω x y) (h0 : (0 : Site d) ∉ s(x, y)) :
    IsOpenEdge d (removeSite 0 (forceOpenFinset G ω)) x y := by
  obtain ⟨hadj, hval⟩ := hopen
  refine ⟨hadj, ?_⟩
  rw [removeSite_apply_of_notMem h0]
  
  have hle := forceOpenFinset_le G ω
  have := hle s(x, y)
  rw [hval] at this
  exact le_antisymm (by simp) this


theorem bka_axis_corridor_step (j : Fin d) (L : ℕ) (hL : 1 ≤ L) :
    Relation.ReflTransGen (CorridorStep (hrHD_corridorEdges j L))
      (hrHD_rayPt j 1) (hrHD_rayPt j (L : ℤ)) :=
  bcc_axisCorridor_corridorStep j L hL


theorem bka_three_independent_axis_neighbours {j₁ j₂ j₃ : Fin d}
    (h12 : j₁ ≠ j₂) (h13 : j₁ ≠ j₃) (h23 : j₂ ≠ j₃) :
    (hrHD_rayPt j₁ 1 ≠ hrHD_rayPt j₂ 1 ∧ hrHD_rayPt j₁ 1 ≠ hrHD_rayPt j₃ 1 ∧
      hrHD_rayPt j₂ 1 ≠ hrHD_rayPt j₃ 1) ∧
    ((hypercubicLattice d).Adj 0 (hrHD_rayPt j₁ 1) ∧
      (hypercubicLattice d).Adj 0 (hrHD_rayPt j₂ 1) ∧
      (hypercubicLattice d).Adj 0 (hrHD_rayPt j₃ 1)) ∧
    (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₁ s ≠ hrHD_rayPt j₂ t) ∧
    (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₁ s ≠ hrHD_rayPt j₃ t) ∧
    (∀ s t : ℤ, s ≠ 0 → hrHD_rayPt j₂ s ≠ hrHD_rayPt j₃ t) :=
  ⟨⟨hrHD_rayPt_one_ne_of_ne h12, hrHD_rayPt_one_ne_of_ne h13, hrHD_rayPt_one_ne_of_ne h23⟩,
    ⟨hrHD_adj_origin_rayPt_one j₁, hrHD_adj_origin_rayPt_one j₂, hrHD_adj_origin_rayPt_one j₃⟩,
    fun _ _ hs => hrHD_rayPt_disjoint_of_ne h12 hs,
    fun _ _ hs => hrHD_rayPt_disjoint_of_ne h13 hs,
    fun _ _ hs => hrHD_rayPt_disjoint_of_ne h23 hs⟩


end Percolation
end StatMech
