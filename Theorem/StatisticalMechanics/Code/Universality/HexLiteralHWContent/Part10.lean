/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part10


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


@[simp] theorem hhc_literalLower_turns (a : ℂ) (h0 : ℤ) (N : ℕ)
    (d : hhc_Dn a h0 N) :
    hhc_halfTurns (hhc_literalLower a h0 N d) =
      d.1.take (hexW2_cutPos h0 d.1) := by
  simp [hhc_literalLower]

@[simp] theorem hhc_literalUpper_turns (a : ℂ) (h0 : ℤ) (N : ℕ)
    (d : hhc_Dn a h0 N) :
    hhc_halfTurns (hhc_literalUpper a h0 N d) =
      d.1.drop (hexW2_cutPos h0 d.1) := by
  simp [hhc_literalUpper]


theorem hhc_literalHighest_reconstruct (a : ℂ) (h0 : ℤ) (N : ℕ)
    (d : hhc_Dn a h0 N) :
    d.1 = hhc_halfTurns (hhc_literalLower a h0 N d) ++
      hhc_halfTurns (hhc_literalUpper a h0 N d) := by
  rw [hhc_literalLower_turns, hhc_literalUpper_turns]
  exact (List.take_append_drop (hexW2_cutPos h0 d.1) d.1).symm


theorem hhc_literalHighest_bridgeDecomp_reconstruct (a : ℂ) (h0 : ℤ) (N : ℕ)
    (d : hhc_Dn a h0 N) :
    d.1 =
      (hexHW_bridge_decomp (hhc_literalLower a h0 N d) : List (ℕ × ℤ)).map Prod.snd ++
      (hexHW_bridge_decomp (hhc_literalUpper a h0 N d) : List (ℕ × ℤ)).map Prod.snd := by
  rw [hhc_bridge_decomp_retains_turns, hhc_bridge_decomp_retains_turns]
  exact hhc_literalHighest_reconstruct a h0 N d


theorem hhc_literalHighest_cut_spec (a : ℂ) (h0 : ℤ) (N : ℕ)
    (d : hhc_Dn a h0 N) :
    hexW2_cutPos h0 d.1 ≤ d.1.length ∧
      (∀ k ≤ d.1.length,
        hexW2_partialDisp h0 d.1 k ≤
          hexW2_partialDisp h0 d.1 (hexW2_cutPos h0 d.1)) ∧
      (∀ k, k < hexW2_cutPos h0 d.1 →
        hexW2_partialDisp h0 d.1 k <
          hexW2_partialDisp h0 d.1 (hexW2_cutPos h0 d.1)) :=
  ⟨hexW2_cutPos_le h0 d.1, hexW2_cutPos_max h0 d.1,
    hexW2_cutPos_first h0 d.1⟩


theorem hhc_literalHighest_halves_legal (a : ℂ) (h0 : ℤ) (N : ℕ)
    (d : hhc_Dn a h0 N) :
    (ofTurns a h0 (hhc_halfTurns (hhc_literalLower a h0 N d))).IsLegalSAW ∧
      (ofTurns (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
        (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum)
        (hhc_halfTurns (hhc_literalUpper a h0 N d))).IsLegalSAW := by
  have hleg := (hhc_Dn_spec a h0 N d).1
  rw [hhc_literalLower_turns, hhc_literalUpper_turns]
  exact ⟨hexW2_prefix_legal a h0 d.1 hleg,
    hexW2_suffix_legal a h0 d.1 hleg⟩


end StatMech.Universality
