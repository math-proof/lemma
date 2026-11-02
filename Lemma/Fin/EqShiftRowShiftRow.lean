import Lemma.Fin.ShiftRow.eq.Ite
open Fin


@[path]
private lemma main
-- given
  (a b i : Fin n) :
-- imply
  (i.shiftRow a b).shiftRow b a = i := by
-- proof
  apply Fin.ext
  simp only [ShiftRow.eq.Ite]
  split_ifs <;> omega


-- created on 2026-11-01
