/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Def.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part5


namespace StatMech.Onsager

@[simp] theorem ons_decEdgeRoute_support
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    (ons_decEdgeRoute L d e hde).support =
      ons_decEdgeRouteVertices L d e := by
  letI : Fact (2 < 8 * L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  simp [ons_decEdgeRoute, ons_fourDirStepWalk,
    ons_decEdgeRouteVertices, ons_fourDirSteps, SimpleGraph.Walk.support]

@[simp] theorem ons_decEdgeRouteVertices_length
    (L : ℕ) (d e : ons_Dart L) :
    (ons_decEdgeRouteVertices L d e).length = 5 := by
  simp [ons_decEdgeRouteVertices]

theorem ons_decEmbed_smallIntCast_eq_iff
    (L : ℕ) [Fact (2 < L)] {a b : ℤ}
    (ha₀ : -4 ≤ a) (ha₁ : a ≤ 12) (hb₀ : -4 ≤ b) (hb₁ : b ≤ 12) :
    (a : ZMod (8 * L)) = (b : ZMod (8 * L)) ↔ a = b := by
  constructor
  · intro hab
    have hz : ((a - b : ℤ) : ZMod (8 * L)) = 0 := by
      push_cast
      linear_combination hab
    rw [CharP.intCast_eq_zero_iff (ZMod (8 * L)) (8 * L)] at hz
    have hL : 24 ≤ (8 * L : ℕ) := by
      have := (Fact.out : 2 < L)
      omega
    have hLz : (24 : ℤ) ≤ (8 * L : ℕ) := by exact_mod_cast hL
    have habs : |a - b| < (8 * L : ℕ) := by
      rw [abs_lt]
      constructor <;> omega
    have hz' : a - b = 0 := Int.eq_zero_of_abs_lt_dvd hz habs
    omega
  · exact congrArg (· : ℤ → ZMod (8 * L))


theorem ons_decEdgeRoute_isPath
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    (ons_decEdgeRoute L d e hde).IsPath := by
  have hne (a b : ℤ) (ha₀ : -4 ≤ a) (ha₁ : a ≤ 12)
      (hb₀ : -4 ≤ b) (hb₁ : b ≤ 12) (hab : a ≠ b) :
      (a : ZMod (8 * L)) ≠ (b : ZMod (8 * L)) := by
    intro h
    exact hab ((ons_decEmbed_smallIntCast_eq_iff L ha₀ ha₁ hb₀ hb₁).mp h)
  have h10 : (1 : ZMod (8 * L)) ≠ 0 := by
    simpa only [Int.cast_one, Int.cast_zero] using
      (hne 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h20 : (2 : ZMod (8 * L)) ≠ 0 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat, Int.cast_zero] using
      (hne 2 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h68 : (6 : ZMod (8 * L)) ≠ 8 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 6 8 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h69 : (6 : ZMod (8 * L)) ≠ 9 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 6 9 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h610 : (6 : ZMod (8 * L)) ≠ 10 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 6 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h21 : (2 : ZMod (8 * L)) ≠ 1 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat, Int.cast_one] using
      (hne 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h2m1 : (2 : ZMod (8 * L)) ≠ -1 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat, Int.cast_neg, Int.cast_one] using
      (hne 2 (-1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h2m2 : (2 : ZMod (8 * L)) ≠ -2 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat, Int.cast_neg] using
      (hne 2 (-2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h46 : (4 : ZMod (8 * L)) ≠ 6 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 4 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h65 : (6 : ZMod (8 * L)) ≠ 5 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 6 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h64 : (6 : ZMod (8 * L)) ≠ 4 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 6 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h43 : (4 : ZMod (8 * L)) ≠ 3 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 4 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h42 : (4 : ZMod (8 * L)) ≠ 2 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 4 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have h24 : (2 : ZMod (8 * L)) ≠ 4 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using
      (hne 2 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  rw [SimpleGraph.Walk.isPath_def, ons_decEdgeRoute_support]
  change ons_decAdj L d e at hde
  rcases hde with hrev | hint
  · subst e
    rcases d with ⟨⟨x, y⟩, mu⟩
    fin_cases mu <;>
      simp [ons_decEdgeRouteVertices, ons_decEdgeRouteDirs,
        ons_decEmbedVertex, ons_decEmbedOffset, ons_dartRev, ons_dirStep] <;>
      ring_nf <;>
      simp [h10, h20, h68, h69, h610, h21, h2m1, h2m2]
  · rcases d with ⟨p, mu⟩
    rcases e with ⟨q, nu⟩
    have hpq : p = q := hint.1
    subst q
    fin_cases mu <;> fin_cases nu <;>
      simp [ons_decInternalAdj, ons_decEdgeRouteVertices,
        ons_decEdgeRouteDirs, ons_decEmbedVertex, ons_decEmbedOffset,
        ons_dartRev, ons_dirStep] at hint ⊢ <;>
      ring_nf <;>
      simp [h10, h46, h65, h64, h43, h42, h24]


end StatMech.Onsager
