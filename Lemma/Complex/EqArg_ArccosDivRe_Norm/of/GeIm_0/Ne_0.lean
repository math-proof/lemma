import Lemma.Complex.Arg.eq.Ite_Arcsin_Ite_AddIte_Arcsin
open Complex


@[main]
private lemma main
  {z : ℂ}
-- given
  (h : z ≠ 0)
  (h_GeIm_0 : im z ≥ 0) :
-- imply
  arg z = arccos (re z / ‖z‖) :=
-- proof
  arg_of_im_nonneg_of_ne_zero h_GeIm_0 h


-- created on 2025-01-13
