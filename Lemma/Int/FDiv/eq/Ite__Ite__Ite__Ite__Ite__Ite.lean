import Lemma.Bool.BFn_Ite.is.Imp.Imp
import Lemma.Bool.Imp.of.Cond
import Lemma.Int.FDiv.eq.Ite__Ite__Ite__Ite__Ite
open Bool Int


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  n // d =
    if n = 0 then
      0
    else if n ≥ 0 ∧ d ≥ 0 then
      n / d
    else if n > 0 ∧ d < 0 then
      -((n - 1) / -d + 1)
    else if n < 0 ∧ d = 0 then
      0
    else if n < 0 ∧ d > 0 then
      -((-n - 1) / d + 1)
    else
      -n / -d := by
-- proof
  -- Split the proof into cases based on the conditions provided.
  apply BFn_Ite.of.Imp.Imp
  intro h
  rw [h]
  norm_num
  apply Imp.of.Cond
  apply FDiv.eq.Ite__Ite__Ite__Ite__Ite


-- created on 2025-03-21
-- updated on 2025-03-27
