/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DiophantineApproximation/ThreeGap.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.NumberTheory.Real.Irrational
/-!
# The three-gap theorem

This file proves that the fractional parts of the first `n` multiples of an irrational real
number cut the circle into gaps of at most three distinct lengths. If three lengths occur, the
largest is the sum of the other two.
-/


namespace MetaMathlibExt

noncomputable def threeGap_fract (α : ℝ) (m : ℤ) : ℝ :=
  Int.fract ((m : ℝ) * α)

noncomputable def threeGap_natFract (α : ℝ) (k : ℕ) : ℝ :=
  threeGap_fract α (k : ℤ)

noncomputable def threeGap_distance (α : ℝ) (k j : ℕ) : ℝ :=
  threeGap_fract α ((j : ℤ) - (k : ℤ))

/-- The points on the circle represented by the first `n` fractional multiples of `α`. -/
def IsThreeGapPoint (n : ℕ) (α x : ℝ) : Prop :=
  ∃ k : ℕ, k < n ∧ x = Int.fract ((k : ℝ) * α)

/-- A length of one of the cyclic gaps between consecutive fractional multiples. -/
def IsThreeGapLength (n : ℕ) (α d : ℝ) : Prop :=
  (∃ x y : ℝ, IsThreeGapPoint n α x ∧ IsThreeGapPoint n α y ∧ x < y ∧
    (∀ z : ℝ, IsThreeGapPoint n α z → x < z → z < y → False) ∧ d = y - x) ∨
  (∃ xlo xhi : ℝ, IsThreeGapPoint n α xlo ∧ IsThreeGapPoint n α xhi ∧
    (∀ z : ℝ, IsThreeGapPoint n α z → z ≤ xhi) ∧
    (∀ z : ℝ, IsThreeGapPoint n α z → xlo ≤ z) ∧ d = 1 + xlo - xhi)

end MetaMathlibExt
