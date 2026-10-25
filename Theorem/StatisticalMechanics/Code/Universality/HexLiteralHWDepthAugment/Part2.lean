/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthAugment


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhda_cutPos_le (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) :
    hlhda_cutPos ts hleg ≤ ts.length :=
  (hlhda_exists_firstMax ts hleg).choose_spec.1

theorem hlhda_cutPos_max (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (k : ℕ) (hk : k ≤ ts.length) :
    hlhd_depth ts hleg k ≤ hlhd_depth ts hleg (hlhda_cutPos ts hleg) :=
  (hlhda_exists_firstMax ts hleg).choose_spec.2.1 k hk

theorem hlhda_cutPos_first (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (k : ℕ) (hk : k < hlhda_cutPos ts hleg) :
    hlhd_depth ts hleg k < hlhd_depth ts hleg (hlhda_cutPos ts hleg) :=
  (hlhda_exists_firstMax ts hleg).choose_spec.2.2 k hk

theorem hlhda_cutPos_pos {ts : List ℤ}
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW) (hne : ts ≠ []) :
    0 < hlhda_cutPos ts hleg := by
  obtain ⟨t, us, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hmax := hlhda_cutPos_max (t :: us) hleg 1 (by simp)
  rw [hlhda_depth_one t us hleg] at hmax
  by_contra hpos
  have hzero : hlhda_cutPos (t :: us) hleg = 0 := Nat.eq_zero_of_not_pos hpos
  rw [hzero, hlhda_depth_zero] at hmax
  omega


end
end StatMech.Universality
