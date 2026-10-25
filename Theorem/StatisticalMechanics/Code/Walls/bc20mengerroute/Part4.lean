/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc19menger.Part5
import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part3
import Theorem.StatisticalMechanics.Code.Percolation.AvoidingAttachment.Part3
import Def.StatisticalMechanics.Code.Walls.bc20mengerroute.Part4
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech.Walls

variable {d : ℕ}


universe u

variable {V : Type u} [DecidableEq V] {GG : SimpleGraph V}

theorem bc20_shellReach_at (d m R : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hmin : ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω)
      (bc20_shellV d m R) (bc20_boundaryV d m) C → 2 ≤ C.ncard) :
    ∃ (u z : Site d), u ∈ vertexBoundary d R ∧ z ∈ vertexBoundary d m ∧
      Connected d (removeSite 0 ω) u z := by
  obtain ⟨u, v, p, hu, hv, hp0⟩ := bc20_origin_avoiding_boxPath_of_min2 d m ω hmin
  exact ⟨(u : Site d), (v : Site d), hu, hv,
    bc20_connected_removeSite_of_avoiding ω (bc20_mapWalk d m ω p)
      (bc20_origin_avoid_of_boxAvoid d m ω p hp0)⟩


theorem bc20_exists_shellVertex_infinite (d R : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (hmin : ∀ m : ℕ, ∀ C, bc16_IsSeparator (bc20_boxGraph d m ω)
      (bc20_shellV d m R) (bc20_boundaryV d m) C → 2 ≤ C.ncard) :
    ∃ u ∈ vertexBoundary d R, (cluster d (removeSite 0 ω) u).Infinite := by
  classical
  choose us zs hus hzs hconns using fun m => bc20_shellReach_at d m R ω (hmin m)
  set Vb := vertexBoundary d R with hVb
  haveI : Finite Vb := vertexBoundary_finite d R
  let f : ℕ → Vb := fun m => ⟨us m, hus m⟩
  have hpig : ∃ u : Vb, {m | f m = u}.Infinite := by
    by_contra h
    push Not at h
    have hsub : (Set.univ : Set ℕ) ⊆ ⋃ u : Vb, {m | f m = u} := fun m _ =>
      Set.mem_iUnion.mpr ⟨f m, rfl⟩
    exact Set.infinite_univ ((Set.finite_iUnion h).subset hsub)
  obtain ⟨⟨u, huVb⟩, hinf⟩ := hpig
  refine ⟨u, huVb, ?_⟩
  rw [cluster_infinite_iff]
  intro n
  obtain ⟨m, hmS, hmge⟩ := hinf.exists_gt (n + 1)
  simp only [Set.mem_setOf_eq] at hmS
  have huseq : us m = u := congrArg Subtype.val hmS
  refine ⟨zs m, ?_, by rw [← huseq]; exact hconns m⟩
  exact fun hzn => (hzs m).2 (box_mono d (by omega : n ≤ m - 1) hzn)


theorem bc20_removeSite_cluster_ne (ω : ConfigSpace (Sym2 (Site d))) (a₁ a₂ : Site d)
    (hne : cluster d ω a₁ ≠ cluster d ω a₂) :
    cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ := by
  have hle : removeSite (0 : Site d) ω ≤ ω := by
    intro e; unfold removeSite; by_cases h : (0 : Site d) ∈ e <;> simp [h]
  exact cluster_ne_of_disjoint (removeSite 0 ω) a₁ a₂ (cluster d ω a₁) (cluster d ω a₂)
    (cluster_mono hle a₁) (cluster_mono hle a₂) (mng_disjoint_of_cluster_ne ω a₁ a₂ hne)


end StatMech.Walls
