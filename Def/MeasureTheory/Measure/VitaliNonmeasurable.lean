/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Measure/VitaliNonmeasurable.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
/-!
# Vitali non-measurable set

Vitali's existence of a subset of `ℝ` that is not Lebesgue measurable,
via choice of representatives in `[0, 1]` for translation by rationals.
-/


namespace MeasureTheory

def vitaliRel (x y : ℝ) : Prop := ∃ q : Rat, x - y = (q : ℝ)

def vitaliSetoid : Setoid ℝ where
  r := vitaliRel
  iseqv :=
    { refl := fun x => ⟨0, by simp⟩
      symm := fun h => by
        obtain ⟨q, hq⟩ := h
        exact ⟨-q, by rw [Rat.cast_neg, ← hq]; ring⟩
      trans := fun h1 h2 => by
        obtain ⟨q1, h1⟩ := h1
        obtain ⟨q2, h2⟩ := h2
        exact ⟨q1 + q2, by rw [Rat.cast_add, ← h1, ← h2]; ring⟩ }

open Classical in
noncomputable def vitaliChoice : Quotient vitaliSetoid → ℝ :=
  fun q =>
    if h : ∃ y, Quotient.mk vitaliSetoid y = q ∧ y ∈ Set.Icc (0 : ℝ) 1 then
      Classical.choose h
    else 0

noncomputable def vitaliSet : Set ℝ :=
  { x | ∃ q, (∃ y, Quotient.mk vitaliSetoid y = q ∧ y ∈ Set.Icc (0 : ℝ) 1) ∧ vitaliChoice q = x }

noncomputable def vitaliTranslate (a : ℝ) : Set ℝ := (fun y => -a + y) ⁻¹' vitaliSet

def RatIcc : Type := { q : Rat // (-1 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ (1 : ℝ) }

def RatIoo : Type := { q : Rat // 0 < q ∧ q < 1 }

end MeasureTheory
