/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhda_returnPos_injective : Function.Injective hexAWReturnPos := by
  intro c d h
  apply hexAWPos_injective
  rw [hexAWPos_eq_returnPos_mul, hexAWPos_eq_returnPos_mul, h]

theorem hlhda_coordRuns_pos_eq (p d : HexReturnCoord) (ts : List ℤ) :
    (hlhr_coordRun p d ts).pos = (hexEndpointCoordRun p d ts).pos := by
  induction ts generalizing p d with
  | nil => rfl
  | cons t ts ih =>
      simpa [hlhr_coordRun, hexEndpointCoordRun] using
        ih (p.add (d.turn t)) (d.turn t)

theorem hlhda_prefixCoord_returnPos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (k : ℕ) :
    (hlhr_coordRun HexReturnCoord.zero HexReturnCoord.base
        (ts.take k)).pos =
      hexAWReturnPos (hlhc_prefixCoord ts hleg.1 k) := by
  rw [hlhda_coordRuns_pos_eq]
  exact hexEndpointCoordRun_pos_eq_aw (ts.take k)
    (hlhc_prefixCoord ts hleg.1 k)
    (by
      intro t ht
      exact hleg.1 t (List.mem_of_mem_take ht))
    (hlhc_prefixCoord_vertex ts hleg.1 k)

@[simp] theorem hlhda_prefixCoord_zero (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    hlhc_prefixCoord ts hleg.1 0 = hexAWOriginCoord := by
  apply hlhda_returnPos_injective
  rw [← hlhda_prefixCoord_returnPos ts hleg 0]
  rfl

@[simp] theorem hlhda_depth_zero (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    hlhd_depth ts hleg 0 = 0 := by
  unfold hlhd_depth
  rw [hlhda_prefixCoord_zero ts hleg]
  rfl

theorem hlhda_depth_one (t : ℤ) (us : List ℤ)
    (hleg : (ofTurns hexAWStart 1 (t :: us)).IsLegalSAW) :
    hlhd_depth (t :: us) hleg 1 = 1 := by
  have ht := hleg.1 t (by simp)
  rcases ht with rfl | rfl
  · have hc : hlhc_prefixCoord ((1 : ℤ) :: us) hleg.1 1 =
        ⟨0, -1, .white⟩ := by
      apply hlhda_returnPos_injective
      rw [← hlhda_prefixCoord_returnPos ((1 : ℤ) :: us) hleg 1]
      simp [hlhr_coordRun, HexReturnCoord.zero, HexReturnCoord.base,
        HexReturnCoord.turn, HexReturnCoord.left, HexReturnCoord.add,
        hexAWReturnPos]
    simp [hlhd_depth, hc, hexAWDepth, hexAWLong]
  · have hc : hlhc_prefixCoord ((-1 : ℤ) :: us) hleg.1 1 =
        ⟨-1, 0, .white⟩ := by
      apply hlhda_returnPos_injective
      rw [← hlhda_prefixCoord_returnPos ((-1 : ℤ) :: us) hleg 1]
      simp [hlhr_coordRun, HexReturnCoord.zero, HexReturnCoord.base,
        HexReturnCoord.turn, HexReturnCoord.right, HexReturnCoord.add,
        hexAWReturnPos]
    simp [hlhd_depth, hc, hexAWDepth, hexAWLong]

theorem hlhda_returnScore_exact (c : HexAWCoord) :
    2 * (hexAWReturnPos c).x - (hexAWReturnPos c).y =
      match c.color with
      | .black => 3 * hexAWDepth c
      | .white => 3 * hexAWDepth c - 2 := by
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp [hexAWReturnPos, hexAWDepth, hexAWLong] <;> omega

theorem hlhda_depth_pos_of_returnScore_pos (c : HexAWCoord)
    (hscore : 0 < 2 * (hexAWReturnPos c).x - (hexAWReturnPos c).y) :
    0 < hexAWDepth c := by
  rcases c with ⟨i, j, color⟩
  cases color <;>
    simp [hexAWReturnPos, hexAWDepth, hexAWLong] at hscore ⊢ <;> omega


theorem hlhda_exists_firstMax (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    ∃ cp, cp ≤ ts.length ∧
      (∀ k ≤ ts.length, hlhd_depth ts hleg k ≤ hlhd_depth ts hleg cp) ∧
      ∀ k, k < cp → hlhd_depth ts hleg k < hlhd_depth ts hleg cp := by
  classical
  set n := ts.length with hn
  set f := fun k => hlhd_depth ts hleg k with hf
  obtain ⟨c, hc, hmax⟩ :=
    Finset.exists_max_image (Finset.range (n + 1)) f ⟨0, by simp⟩
  rw [Finset.mem_range] at hc
  set M := f c with hM
  have hmaxval : ∀ k ≤ n, f k ≤ M := fun k hk =>
    hmax k (Finset.mem_range.mpr (by omega))
  have hex : ∃ k, k ≤ n ∧ f k = M := ⟨c, by omega, rfl⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, ?_⟩
  · intro k hk
    show f k ≤ f (Nat.find hex)
    rw [(Nat.find_spec hex).2]
    exact hmaxval k hk
  · intro k hk
    show f k < f (Nat.find hex)
    have hnot : ¬ (k ≤ n ∧ f k = M) :=
      (Nat.lt_find_iff hex k).mp hk k le_rfl
    have hkn : k ≤ n := by
      have := Nat.find_spec hex
      omega
    have hle := hmaxval k hkn
    rw [(Nat.find_spec hex).2]
    exact lt_of_le_of_ne hle (fun heq => hnot ⟨hkn, heq⟩)

end
end StatMech.Universality
