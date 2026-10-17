import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x ∈ Set.Ioo (-1) 1)
  (h₁ : y ∈ Set.Ioo (-1) 1)
  (h₂ : x < y) :
-- imply
  y * Real.sqrt (1 - x ^ 2) > x * Real.sqrt (1 - y ^ 2) := by
-- proof
  obtain ⟨hx₁, hx₂⟩ := h₀
  obtain ⟨hy₁, hy₂⟩ := h₁
  have hsin : Real.sin (Real.arcsin y - Real.arcsin x) =
      y * Real.cos (Real.arcsin x) - x * Real.cos (Real.arcsin y) := by
    rw [Real.sin_sub]
    simp only [Real.sin_arcsin (le_of_lt hx₁) (le_of_lt hx₂),
      Real.sin_arcsin (le_of_lt hy₁) (le_of_lt hy₂)]
    ring
  have hcosx : Real.cos (Real.arcsin x) = Real.sqrt (1 - x ^ 2) := Real.cos_arcsin x
  have hcosy : Real.cos (Real.arcsin y) = Real.sqrt (1 - y ^ 2) := Real.cos_arcsin y
  have hyπ : Real.arcsin y < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hy₂
  have hxπ : -(Real.pi / 2) < Real.arcsin x := by
    rw [neg_lt, ← Real.arcsin_neg]
    exact Real.arcsin_lt_pi_div_two.mpr (by linarith)
  have hpos : 0 < Real.sin (Real.arcsin y - Real.arcsin x) :=
    Real.sin_pos_of_pos_of_lt_pi
      (sub_pos.mpr (Real.arcsin_lt_arcsin (le_of_lt hx₁) h₂ (le_of_lt hy₂)))
      (by linarith [hyπ, hxπ])
  rw [hsin, hcosx, hcosy] at hpos
  linarith


-- created on 2026-10-11
-- updated on 2026-10-17
