import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {a b c : ℝ}
  -- given
  (hlt : a < b)
  (hneg : c < 0)
  -- imply
  : b / c < a / c := by
  -- proof
  have hdiff : (b - a) / c < 0 := by
    apply div_neg_of_pos_of_neg <;> linarith
  have h : b / c - a / c = (b - a) / c := by
    field_simp
  linarith

-- created on 2023-03-26
