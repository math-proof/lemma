/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part9
open Finset Matrix


namespace StatMech.FrontierD

theorem zip_map_same_particleHole {ι α β : Type*}
    (l : List ι) (f : ι → α) (g : ι → β) :
    (l.map f).zip (l.map g) = l.map fun i => (f i, g i) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem pairwise_flatMap_pairs_elim {ι α : Type*} [Preorder α]
    (f g : ι → α) {l : List ι}
    (h : (l.flatMap fun i => [f i, g i]).Pairwise (· ≤ ·)) :
    (∀ i ∈ l, f i ≤ g i) ∧ l.Pairwise (fun i j => g i ≤ f j) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      change List.Pairwise (· ≤ ·)
        (f a :: g a :: (l.flatMap fun i => [f i, g i])) at h
      rw [List.pairwise_cons_cons_iff_of_trans] at h
      obtain ⟨hsame, htail⟩ := h
      rw [List.pairwise_cons] at htail
      obtain ⟨hcross, hrest⟩ := htail
      obtain ⟨ihsame, ihcross⟩ := ih hrest
      constructor
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | hi
        · exact hsame
        · exact ihsame i hi
      · rw [List.pairwise_cons]
        refine ⟨?_, ihcross⟩
        intro j hj
        apply hcross (f j)
        exact List.mem_flatMap.mpr ⟨j, hj, by simp⟩

theorem sixVertexPositionsForwardInterlaced_of_forward {N n : ℕ}
    (x y : SixVertexSector N n)
    (h : SixVertexForwardInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y)) :
    SixVertexPositionsForwardInterlaced x y := by
  rw [SixVertexForwardInterlaced] at h
  rw [sixVertexAlternating, sixVertexSector_upPositions_eq_map_position,
    sixVertexSector_upPositions_eq_map_position, zip_map_same_particleHole] at h
  simp only [List.flatMap_map] at h
  obtain ⟨hsame, hcross⟩ := pairwise_flatMap_pairs_elim
    (sixVertexSectorPosition x) (sixVertexSectorPosition y) h.2
  constructor
  · intro i
    exact hsame i (by simp)
  · intro k hk
    have hrel := (List.pairwise_iff_getElem.mp hcross) k (k + 1)
      (by simp; omega) (by simp; omega) (by omega)
    simpa using hrel


end StatMech.FrontierD
