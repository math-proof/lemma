/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part9


namespace StatMech.Universality

open HexWalk

noncomputable section

@[simp] theorem hlhd_normalizeHeading_true (h : Fin 6) :
    hlhd_normalizeHeading true h = h := rfl

@[simp] theorem hlhd_normalizeHeading_false (h : Fin 6) :
    hlhd_normalizeHeading false h = h + 3 := rfl

theorem hlhd_edgeOfHeading_normalize (up : Bool) (source c : HexAWCoord)
    (h : Fin 6) :
    hlhd_edgeOfHeading (hlhd_normalizeCoord up source c)
        (hlhd_normalizeHeading up h) =
      hlhd_edgeOfHeading c h := by
  rcases source with ⟨si, sj, sc⟩
  rcases c with ⟨i, j, color⟩
  cases up <;> cases color <;> fin_cases h <;>
    simp [hlhd_normalizeCoord, hlhd_normalizeHeading, hlhd_swapColor,
      hlhd_edgeOfHeading]

theorem hlhd_normalizeHeading_turn (up : Bool) (h : Fin 6) (t : ℤ)
    (ht : t = 1 ∨ t = -1) :
    hlhd_normalizeHeading up (hexHeadingTurn h t) =
      hexHeadingTurn (hlhd_normalizeHeading up h) t := by
  rcases ht with rfl | rfl <;> cases up <;> fin_cases h <;> decide


theorem hlhd_coordPath_normalize (up : Bool) (source c : HexAWCoord)
    (h : Fin 6) (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    (hlhd_coordPath c h ts).map (hlhd_normalizeCoord up source) =
      hlhd_coordPath (hlhd_normalizeCoord up source c)
        (hlhd_normalizeHeading up h) ts := by
  induction ts generalizing c h with
  | nil =>
      simp [hlhd_coordPath, hlhd_edgeOfHeading_normalize,
        hlhd_normalizeCoord_neighbor]
  | cons t ts ih =>
      have ht : t = 1 ∨ t = -1 := hlegal t (by simp)
      have htail : ∀ u ∈ ts, u = 1 ∨ u = -1 := by
        intro u hu
        exact hlegal u (by simp [hu])
      simp only [hlhd_coordPath, List.map_cons, List.cons.injEq, true_and]
      rw [ih _ _ htail, hlhd_normalizeCoord_neighbor,
        hlhd_edgeOfHeading_normalize,
        hlhd_normalizeHeading_turn up h t ht]

theorem hlhd_interval_source_normalizes (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    hlhd_normalizeCoord (hlhd_intervalUp ts hleg hhalf p hp)
        (hlhc_prefixCoord ts hleg.1 p.1)
        (hlhc_prefixCoord ts hleg.1 p.1) = hexAWOriginCoord := by
  have hc := hlhd_bridge_source_color ts hleg p
    (hlhd_interval_index_bounds ts hleg hhalf p hp).2
    (hlhd_intervalUp_bridge ts hleg hhalf p hp)
  rcases hc with ⟨hup, hblack⟩ | ⟨hup, hwhite⟩
  · rw [hup]
    exact hlhd_normalizeCoord_source_up _ hblack
  · rw [hup]
    exact hlhd_normalizeCoord_source_down _ hwhite


end
end StatMech.Universality
