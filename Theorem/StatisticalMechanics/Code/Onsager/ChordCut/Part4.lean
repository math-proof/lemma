/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Onsager.ChordCut.Part5


namespace StatMech.Onsager.ChordCut

open scoped BigOperators


theorem rayX_injective (w : Pt) : Function.Injective (rayX w) := by
  intro a b hab
  simp only [rayX, Prod.mk.injEq] at hab
  have : (a : ℤ) = (b : ℤ) := by omega
  exact_mod_cast this


theorem chordInterior_nodup (w : Pt) (k : ℕ) : (chordInterior w k).Nodup := by
  unfold chordInterior
  exact (List.nodup_range').map (rayX_injective w)


theorem chordInterior_disjoint_boundary (D : BoxData) (w : Pt) (k : ℕ) (arc : List Pt)
    (harc : ∀ p ∈ arc, p ∈ D.B)
    (hint : ∀ p ∈ chordInterior w k, p ∉ D.B) :
    arc.Disjoint (chordInterior w k) := by
  intro p hpa hpc
  exact hint p hpc (harc p hpa)


theorem chordInterior_offBoundary (D : BoxData) (w : Pt) (k : ℕ)
    (hfh : ∀ j : ℕ, 1 ≤ j → j < k → rayX w j ∉ D.B) :
    ∀ p ∈ chordInterior w k, p ∉ D.B := by
  intro p hp
  unfold chordInterior at hp
  rw [List.mem_map] at hp
  obtain ⟨j, hj, rfl⟩ := hp
  rw [List.mem_range'] at hj
  obtain ⟨i, hik, rfl⟩ := hj
  exact hfh (1 + 1 * i) (by omega) (by omega)


theorem chord_piece_nodup (D : BoxData) (w : Pt) (k : ℕ) (arc : List Pt)
    (harcND : arc.Nodup) (harc : ∀ p ∈ arc, p ∈ D.B)
    (hint : ∀ p ∈ chordInterior w k, p ∉ D.B) :
    (arc ++ chordInterior w k).Nodup := by
  exact List.Nodup.append harcND (chordInterior_nodup w k)
    (chordInterior_disjoint_boundary D w k arc harc hint)


end StatMech.Onsager.ChordCut
