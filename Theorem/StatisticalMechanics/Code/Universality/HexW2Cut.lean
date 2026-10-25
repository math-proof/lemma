/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraCut
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Def.StatisticalMechanics.Code.Universality.HexW2Cut


namespace StatMech.Universality

open HexWalk List Filter

open scoped BigOperators Real


theorem hexW2_exists_firstArgmax (h0 : ℤ) (ts : List ℤ) :
    ∃ cp, cp ≤ ts.length
      ∧ (∀ k ≤ ts.length, hexW2_partialDisp h0 ts k ≤ hexW2_partialDisp h0 ts cp)
      ∧ (∀ k, k < cp → hexW2_partialDisp h0 ts k < hexW2_partialDisp h0 ts cp) := by
  classical
  set n := ts.length with hn
  set f := fun k => hexW2_partialDisp h0 ts k with hf
  obtain ⟨c, hc_mem, hc_max⟩ :=
    Finset.exists_max_image (Finset.range (n + 1)) f ⟨0, by simp⟩
  rw [Finset.mem_range] at hc_mem
  set M := f c with hM
  have hmaxval : ∀ k ≤ n, f k ≤ M := fun k hk =>
    hc_max k (Finset.mem_range.mpr (by omega))
  have hexP : ∃ k, k ≤ n ∧ f k = M := ⟨c, by omega, rfl⟩
  refine ⟨Nat.find hexP, (Nat.find_spec hexP).1, ?_, ?_⟩
  · intro k hk
    show f k ≤ f (Nat.find hexP)
    rw [(Nat.find_spec hexP).2]
    exact hmaxval k hk
  · intro k hkcp
    show f k < f (Nat.find hexP)
    have hnotP : ¬ (k ≤ n ∧ f k = M) :=
      (Nat.lt_find_iff hexP k).mp hkcp k le_rfl
    have hkn : k ≤ n := by have := Nat.find_spec hexP; omega
    have hle : f k ≤ M := hmaxval k hkn
    rw [(Nat.find_spec hexP).2]
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd ⟨hkn, h⟩ hnotP


end StatMech.Universality
