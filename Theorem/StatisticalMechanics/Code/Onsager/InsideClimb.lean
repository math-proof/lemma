/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InsideClimb.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.SingleTopRun
import Theorem.StatisticalMechanics.Code.Onsager.NoDoubleWind2.Part2


namespace StatMech.Onsager.InsideClimb

open Finset StatMech.Onsager.BaseCase StatMech.Onsager.WalkCrossing
  StatMech.Onsager.NoDoubleWind StatMech.Onsager.JordanParity

variable {n : ℕ} [NeZero n]


theorem inside_climb_x (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0) (a b : ℤ)
    (hinside : rayParity d a b = 1)
    (hstr : ∀ k : Fin n, isVertEdge (d k) → (pos d k).1 = a + 1 →
      ¬ (min ((pos d k).2) ((pos d (k + 1)).2) ≤ b ∧
         b < max ((pos d k).2) ((pos d (k + 1)).2))) :
    rayParity d (a + 1) b = 1 := by
  rw [← rayParity_hstep d hclosed a b hstr]; exact hinside


theorem inside_climb_y (d : Fin n → Fin 4) (a b : ℤ)
    (hinside : rayParity d a b = 1)
    (h : ∀ k : Fin n, isHorizEdge (d k) →
      min ((pos d k).1) ((pos d (k + 1)).1) = a → (pos d k).2 ≠ b + 1) :
    rayParity d a (b + 1) = 1 := by
  rw [← rayParity_vstep d a b h]; exact hinside


theorem nw_corner_coords (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (i : Fin n) (hN : d i = 1) (hW : d (i + 1) = 2) :
    pos d i = ((pos d (i + 1)).1, (pos d (i + 1)).2 - 1) ∧
      pos d (i + 1 + 1) = ((pos d (i + 1)).1 - 1, (pos d (i + 1)).2) := by
  have hs1 := pos_succ d hclosed i
  have hs2 := pos_succ d hclosed (i + 1)
  rw [hN] at hs1
  rw [hW] at hs2
  have e1 : stepOf (1 : Fin 4) = (0, 1) := rfl
  have e2 : stepOf (2 : Fin 4) = (-1, 0) := rfl
  rw [e1] at hs1
  rw [e2] at hs2
  constructor
  · have hx : (pos d (i + 1)).1 = (pos d i).1 := by rw [hs1]; simp
    have hy : (pos d (i + 1)).2 = (pos d i).2 + 1 := by rw [hs1]; simp
    ext <;> simp only [] <;> omega
  · have hx : (pos d (i + 1 + 1)).1 = (pos d (i + 1)).1 - 1 := by rw [hs2]; simp; omega
    have hy : (pos d (i + 1 + 1)).2 = (pos d (i + 1)).2 := by rw [hs2]; simp
    ext <;> simp only [] <;> omega


theorem nw_corner_not_climbable_x (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (i : Fin n) (hN : d i = 1) (hW : d (i + 1) = 2) :
    ¬ (∀ k : Fin n, isVertEdge (d k) → (pos d k).1 = ((pos d (i + 1)).1 - 1) + 1 →
        ¬ (min ((pos d k).2) ((pos d (k + 1)).2) ≤ (pos d (i + 1)).2 - 1 ∧
           (pos d (i + 1)).2 - 1 < max ((pos d k).2) ((pos d (k + 1)).2))) := by
  intro hstr
  obtain ⟨hpi, _⟩ := nw_corner_coords d hclosed i hN hW
  have hvert : isVertEdge (d i) := Or.inl hN
  have hcol : (pos d i).1 = ((pos d (i + 1)).1 - 1) + 1 := by rw [hpi]; simp
  have hpi2 : (pos d i).2 = (pos d (i + 1)).2 - 1 := by rw [hpi]
  refine hstr i hvert hcol ?_
  refine ⟨?_, ?_⟩ <;> rw [hpi2] <;> omega


theorem nw_corner_not_climbable_y (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (i : Fin n) (hN : d i = 1) (hW : d (i + 1) = 2) :
    ¬ (∀ k : Fin n, isHorizEdge (d k) →
        min ((pos d k).1) ((pos d (k + 1)).1) = (pos d (i + 1)).1 - 1 →
        (pos d k).2 ≠ ((pos d (i + 1)).2 - 1) + 1) := by
  intro h
  obtain ⟨_, hpi2⟩ := nw_corner_coords d hclosed i hN hW
  have hhoriz : isHorizEdge (d (i + 1)) := Or.inr hW
  have hcol : min ((pos d (i + 1)).1) ((pos d (i + 1 + 1)).1) = (pos d (i + 1)).1 - 1 := by
    rw [hpi2]; simp only []; omega
  have hht : (pos d (i + 1)).2 = ((pos d (i + 1)).2 - 1) + 1 := by omega
  exact h (i + 1) hhoriz hcol hht


theorem lexmax_unique (d : Fin n → Fin 4) (hsimple : Function.Injective (pos d))
    {M M' : Fin n} (hM : ∀ j : Fin n, toLex (pos d j) ≤ toLex (pos d M))
    (hM' : ∀ j : Fin n, toLex (pos d j) ≤ toLex (pos d M')) :
    M = M' := by
  have h1 : toLex (pos d M) ≤ toLex (pos d M') := hM' M
  have h2 : toLex (pos d M') ≤ toLex (pos d M) := hM M'
  have heq : toLex (pos d M) = toLex (pos d M') := le_antisymm h1 h2
  exact hsimple (toLex_inj.mp heq)


theorem exists_lexmax_nw_corner (d : Fin n → Fin 4) (hclosed : ∑ i, stepOf (d i) = 0)
    (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
    ∃ i : Fin n, d i = 1 ∧ d (i + 1) = 2 := by
  obtain ⟨M, hin, hout⟩ := lexmax_corner d hclosed hreflexfree
  exact ⟨M - 1, hin, by rw [sub_add_cancel]; exact hout⟩


end StatMech.Onsager.InsideClimb
