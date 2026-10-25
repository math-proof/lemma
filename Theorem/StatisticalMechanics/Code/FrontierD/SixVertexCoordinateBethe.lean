/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricProduct.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part9
import Mathlib.GroupTheory.Perm.Fin
open Finset Matrix
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

theorem coordinate_zip_map_same {ι α β : Type*} (l : List ι)
    (f : ι → α) (g : ι → β) :
    (l.map f).zip (l.map g) = l.map fun i => (f i, g i) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem pairwise_flatMap_pairs_onlyIf {ι α : Type*} [Preorder α]
    (f g : ι → α) {l : List ι}
    (h : (l.flatMap fun i => [f i, g i]).Pairwise (· ≤ ·)) :
    (∀ i ∈ l, f i ≤ g i) ∧ l.Pairwise fun i j => g i ≤ f j := by
  induction l with
  | nil => simp
  | cons a l ih =>
      change List.Pairwise (· ≤ ·)
        (f a :: g a :: (l.flatMap fun i => [f i, g i])) at h
      rw [List.pairwise_cons_cons_iff_of_trans] at h
      rw [List.pairwise_cons] at h
      have htail := ih h.2.2
      constructor
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | hi
        · exact h.1
        · exact htail.1 i hi
      · rw [List.pairwise_cons]
        refine ⟨?_, htail.2⟩
        intro j hj
        apply h.2.1
        exact List.mem_flatMap.mpr ⟨j, hj, by simp⟩


theorem sixVertexForwardInterlaced_iff_positions {N n : ℕ}
    (x y : SixVertexSector N n) :
    SixVertexForwardInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) ↔
      SixVertexPositionsForwardInterlaced x y := by
  constructor
  · intro h
    have hp := h.2
    rw [sixVertexAlternating, sixVertexSector_upPositions_eq_map_position,
      sixVertexSector_upPositions_eq_map_position,
      coordinate_zip_map_same] at hp
    simp only [List.flatMap_map] at hp
    have hparts := pairwise_flatMap_pairs_onlyIf
      (sixVertexSectorPosition x) (sixVertexSectorPosition y) hp
    constructor
    · intro i
      exact hparts.1 i (by simp)
    · intro k hk
      have hrel := hparts.2.rel_get_of_lt
        (a := ⟨k, by simpa using (show k < n by omega)⟩)
        (b := ⟨k + 1, by simpa using hk⟩) (by simp)
      simpa using hrel
  · exact sixVertexForwardInterlaced_of_positions x y


end
end StatMech.FrontierD
