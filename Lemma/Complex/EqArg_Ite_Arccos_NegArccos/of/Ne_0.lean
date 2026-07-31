import Lemma.Complex.Arg.eq.Ite__Ite_Arcsin
open Complex


@[main]
private lemma main
  {z : ℂ}
-- given
  (h : z ≠ 0) :
-- imply
  arg z =
    if im z ≥ 0 then
      arccos (re z / ‖z‖)
    else
      -arccos (re z / ‖z‖) := by
-- proof
  if h_im_neg : im z < 0 then
    simp [h_im_neg.not_ge]
    exact Complex.arg_of_im_neg h_im_neg
  else if h_im_zero : im z = 0 then
    simp [h_im_zero]
    exact Complex.arg_of_im_nonneg_of_ne_zero h_im_zero.ge h
  else
    have h_im_pos : 0 < im z := lt_of_le_of_ne (not_lt.mp h_im_neg) (Ne.symm h_im_zero)
    simp [h_im_pos.le]
    exact Complex.arg_of_im_nonneg_of_ne_zero h_im_pos.le h


-- created on 2025-01-12
-- updated on 2025-04-17
