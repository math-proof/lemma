import Lemma.Algebra.Ite.eq.SubIte
import Lemma.Algebra.SubAdd.eq.Sub_Sub.of.Ge
import Lemma.Algebra.AddAdd.eq.Add_Add
import Lemma.Algebra.EqSubAdd
import Lemma.Bool.BFnIte.is.Imp.Imp
import Lemma.Nat.Add
import Lemma.Algebra.Sub_1.eq.AddDivS_2.of.Odd
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Algebra.Odd.is.NotEven
open Algebra Bool Nat


@[main]
private lemma main
  -- suppose n is the group_size, m is the real num_return_sequences of answers
  {m n : ℕ}
-- given
  (h : m > n) :
-- imply
  let Δ := m - n
  let start := m / 2 - Δ / 2
  let stop :=
  if Δ is even then
    m / 2 + Δ / 2
  else
    m / 2 + Δ / 2 + 1
  stop - start = Δ := by
-- proof
  intro Δ start stop
  simp [start, stop]
  rw [SubIte.eq.Ite]
  repeat rw [Sub_Sub.eq.SubAdd.of.Ge]
  ·
    repeat rw [AddAdd.eq.Add_Add]
    repeat rw [EqSubAdd.left.int]
    apply BFnIte.of.Imp.Imp
    ·
      intro h
      apply EqAddDivS_2.of.Even h
    ·
      intro h
      rw [Add.comm (a := 1)]
      rw [Add_Add.eq.AddAdd]
      have h := Odd.of.NotEven h
      rw [AddDivS_2.eq.Sub_1.of.Odd h]
      rw [EqAddSub.of.Ge]
      omega
  repeat omega


-- created on 2025-08-12
-- updated on 2025-08-13
