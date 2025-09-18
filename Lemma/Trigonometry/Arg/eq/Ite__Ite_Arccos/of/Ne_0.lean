import Lemma.Trigonometry.Arg.eq.Ite__Ite_Arcsin
import Lemma.Logic.BFn_Ite.is.Imp.Imp
open Logic Trigonometry


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
  rw [BFn_Ite.is.Imp.Imp (R := Eq)]
  constructor
  by_cases h_GeRe_0 : re z ≥ 0
  intro h_GeIm_0
  -- rw [Arg.eq.Ite__Ite_Arcsin]
  sorry
  sorry
  sorry


-- created on 2025-01-12
-- updated on 2025-04-17
