/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ChordCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Onsager.ChordCut.Part6


namespace StatMech.Onsager.ChordCut

open scoped BigOperators


theorem chord_of_interiorReaches (D : BoxData) (w : Pt) (_hw : w ∈ D.B)
    (hcore : InteriorReaches D w) :
    ∃ k : ℕ, 1 ≤ k ∧ rayX w k ∈ D.B ∧
      (∀ j : ℕ, 1 ≤ j → j < k → rayX w j ∉ D.B) := by
  classical
  
  have hex' : ∃ k, 1 ≤ k ∧ rayX w k ∈ D.B := hcore
  refine ⟨Nat.find hex', (Nat.find_spec hex').1, (Nat.find_spec hex').2, ?_⟩
  intro j hj1 hjk hjB
  exact Nat.find_min hex' hjk ⟨hj1, hjB⟩


theorem chord_split_of_core (D : BoxData) (w : Pt) (_hw : w ∈ D.B)
    (hcore : InteriorReaches D w) (arc : List Pt)
    (harcND : arc.Nodup) (harc : ∀ p ∈ arc, p ∈ D.B) :
    ∃ k : ℕ, 1 ≤ k ∧ rayX w k ∈ D.B ∧ (arc ++ chordInterior w k).Nodup := by
  obtain ⟨k, hk1, hkB, hoff⟩ := chord_of_interiorReaches D w _hw hcore
  refine ⟨k, hk1, hkB, ?_⟩
  exact chord_piece_nodup D w k arc harcND harc (chordInterior_offBoundary D w k hoff)


end StatMech.Onsager.ChordCut
