import Lemma.Complex.Arg.eq.Ite_Arcsin_Ite_AddIte_Arcsin
open Complex


@[main]
private lemma main
  {z : ℂ} :
-- imply
  arg z =
    if re z ≥ 0 then
      arcsin (im z / ‖z‖)
    else if im z ≥ 0 then
      π - arcsin (im z / ‖z‖)
    else
      -arcsin (im z / ‖z‖) - π := by
-- proof
  rw [Arg.eq.Ite_Arcsin_Ite_AddIte_Arcsin]
  split_ifs with h_re h_im
  · rfl
  ·
    rw [neg_im, neg_div, Real.arcsin_neg]
    ring
  ·
    rw [neg_im, neg_div, Real.arcsin_neg]


-- created on 2026-08-07
