import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {a b c : ℝ}
  -- given
  (hgt : b < a)
  (hneg : c < 0)
  -- imply
  : a / c < b / c := by
  -- proof
  have hdiff : (a - b) / c < 0 := by
    apply div_neg_of_pos_of_neg <;> linarith
  have h : a / c - b / c = (a - b) / c := by
    field_simp
  linarith

-- created on 2023-03-26
